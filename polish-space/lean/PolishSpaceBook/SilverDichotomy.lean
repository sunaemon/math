module

public import PolishSpaceBook.LambdaCoanalyticTruth
public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section

/-!
# Silver's perfect antichain theorem

The parameter is chosen from the analytic nonrelation. The fixed-parameter
kernel, local truth, common-right contradiction and binary fusion then give
the antichain on Baire space. A continuous surjection transfers the theorem
to any nonempty Polish space: although the surjection need not be injective,
it is injective on the antichain because equality implies equivalence.
The surjection is the book's explicit Cauchy-name and retraction construction.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory Topology

/-- Choose one parameter coding the nonrelation of a coanalytic equivalence
relation on Baire space. -/
theorem coanalytic_relation_in_one_parameter (E : Setoid FusionReal)
    (hE : AnalyticSet {p : FusionReal × FusionReal | ¬ E.r p.1 p.2}) :
    ∃ ε : ℕ → ℕ,
      LambdaTree.ProjectedRelation ε (fun x y => ¬ E.r x y) := by
  have hl : Continuous (leftBaire : FusionReal → FusionReal) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => k.unpair.1)).comp (continuous_apply n)
  have hr : Continuous (rightBaire : FusionReal → FusionReal) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => k.unpair.2)).comp (continuous_apply n)
  exact (LambdaTree.analyticSet_iff_exists_parameter _).mp (hE.preimage (hl.prodMk hr))

/-- Silver's antichain theorem on Baire space, with no supplied parameter or
generic splitting hypothesis. -/
theorem silver_antichain_baire (E : Setoid FusionReal)
    (hE : AnalyticSet {p : FusionReal × FusionReal | ¬ E.r p.1 p.2})
    [Uncountable (Quotient E)] :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  obtain ⟨ε, hε⟩ := coanalytic_relation_in_one_parameter E hE
  exact LambdaTree.parameter_silver_antichain ε E hε

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: theorem
  title: Silver fusion
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    If $E$ has uncountably many classes, apply the Silver fusion theorem of §{sec:edst-silver-fusion}, relativized to a
    real parameter coding the space and the coanalytic relation. It gives a continuous injection
    $\pi:\CantorSpace\to X$ whose distinct images are $E$-inequivalent. The image of the compact Cantor space is compact,
    and the continuous injection into the Hausdorff space $X$ is a homeomorphism onto that image. Hence the image is a
    perfect $E$-antichain. Conversely, such an antichain meets uncountably many classes, so the two alternatives are
    mutually exclusive.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For a general Polish $X$ with uncountably many classes, choose the continuous surjection
    $q:\BaireSpace\to X$ constructed in §{sec:universal-continuous-surjection}. Pull $E$ back along $q$. The resulting
    relation is coanalytic and still has uncountably many classes, because the induced map of quotients is surjective.
    Apply the Baire-space construction. The composite $q\circ\pi$ remains an antichain and is injective: equality of two
    images would make the corresponding points equivalent. Its image is compact and homeomorphic to Cantor space,
    hence is a nonempty perfect antichain. Conversely, any Cantor antichain injects Cantor space into the quotient, so the
    countable-class and perfect-antichain alternatives are mutually exclusive.
-/
/-- Silver's perfect antichain construction for every Polish space.
Nonemptiness follows from the uncountable quotient. The continuous
surjection used for transport cannot collapse two antichain points. -/
theorem silver_antichain_polish (X : Type*) [TopologicalSpace X] [PolishSpace X]
    (E : Setoid X) (hE : CoanalyticSet {p : X × X | E.r p.1 p.2})
    [Uncountable (Quotient E)] :
    ∃ π : (ℕ → Bool) → X, Continuous π ∧ Injective π ∧
      ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  classical
  let : Nonempty X := ⟨(Classical.arbitrary (Quotient E)).out⟩
  obtain ⟨q, hq, hqs⟩ := exists_baire_continuous_surjection X
  let R : Setoid FusionReal := Setoid.comap q E
  have hR : AnalyticSet {p : FusionReal × FusionReal | ¬ R.r p.1 p.2} :=
    hE.preimage (hq.prodMap hq)
  have hs : Surjective (Quotient.map q (sa := R) (sb := E) (fun {_ _} h => h)) :=
    Quotient.map_surjective (sa := R) (sb := E) (f := q) (fun {_ _} h => h) hqs
  let : Uncountable (Quotient R) := hs.uncountable
  obtain ⟨π, hc, _, hanti⟩ := silver_antichain_baire R hR
  refine ⟨q ∘ π, hq.comp hc, ?_, hanti⟩
  intro a b hab
  by_contra hn
  apply hanti a b hn
  change E.r (q (π a)) (q (π b))
  change q (π a) = q (π b) at hab
  rw [hab]

/-- The exhaustive alternatives of Silver's theorem. -/
theorem silver_alternatives_polish (X : Type*) [TopologicalSpace X] [PolishSpace X]
    (E : Setoid X) (hE : CoanalyticSet {p : X × X | E.r p.1 p.2}) :
    Countable (Quotient E) ∨
      ∃ π : (ℕ → Bool) → X, Continuous π ∧ Injective π ∧
        ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  classical
  by_cases h : Countable (Quotient E)
  · exact Or.inl h
  · let : Uncountable (Quotient E) := ⟨h⟩
    exact Or.inr (silver_antichain_polish X E hE)

/-- Distinct antichain points give distinct quotient classes, so the two
Silver alternatives cannot both hold. -/
theorem uncountable_quotient_of_cantor_antichain {X : Type*} (E : Setoid X)
    (π : (ℕ → Bool) → X) (hanti : ∀ a b, a ≠ b → ¬ E.r (π a) (π b)) :
    Uncountable (Quotient E) := by
  let : Uncountable (ℕ → Bool) := ⟨cantor_space_not_countable⟩
  have hi : Injective (fun a => Quotient.mk E (π a)) := by
    intro a b hab
    by_contra hn
    exact hanti a b hn (Quotient.exact hab)
  exact hi.uncountable

/-- The image of the constructed Cantor injection is a genuine nonempty
perfect set in the original topology. -/
theorem silver_perfect_antichain_polish (X : Type*) [TopologicalSpace X] [PolishSpace X]
    (E : Setoid X) (hE : CoanalyticSet {p : X × X | E.r p.1 p.2})
    [Uncountable (Quotient E)] :
    ∃ P : Set X, P.Nonempty ∧ Perfect P ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ E.r x y := by
  obtain ⟨π, hc, hi, hanti⟩ := silver_antichain_polish X E hE
  refine ⟨range π, range_nonempty π, ⟨(isCompact_range hc).isClosed, ?_⟩, ?_⟩
  · let : PerfectSpace (ℕ → Bool) := cantor_space_perfect
    rw [preperfect_iff_nhds]
    rintro _ ⟨a, rfl⟩ U hU
    obtain ⟨b, hb, hba⟩ := preperfect_iff_nhds.mp
      (PerfectSpace.univ_preperfect (α := ℕ → Bool)) a (mem_univ a)
      (π ⁻¹' U) (hc.continuousAt hU)
    exact ⟨π b, ⟨hb.1, mem_range_self b⟩, fun h => hba (hi h)⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact hanti a b (fun h => hab (congrArg π h))

/-- Silver's dichotomy, with mutually exclusive alternatives expressed as
an equivalence. -/
theorem silver_dichotomy_polish (X : Type*) [TopologicalSpace X] [PolishSpace X]
    (E : Setoid X) (hE : CoanalyticSet {p : X × X | E.r p.1 p.2}) :
    Uncountable (Quotient E) ↔
      ∃ π : (ℕ → Bool) → X, Continuous π ∧ Injective π ∧
        ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  constructor
  · intro h
    let := h
    exact silver_antichain_polish X E hE
  · rintro ⟨π, _, _, ha⟩
    exact uncountable_quotient_of_cantor_antichain E π ha

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: statement
  kind: theorem
  title: Silver
-/
/-- Silver's theorem in the perfect-antichain formulation printed in Chapter 16. -/
theorem silver_perfect_alternatives_polish
    (X : Type*) [TopologicalSpace X] [PolishSpace X]
    (E : Setoid X) (hE : CoanalyticSet {p : X × X | E.r p.1 p.2}) :
    Countable (Quotient E) ∨
      ∃ P : Set X, P.Nonempty ∧ Perfect P ∧
        ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ E.r x y := by
  classical
  by_cases h : Countable (Quotient E)
  · exact Or.inl h
  · let : Uncountable (Quotient E) := ⟨h⟩
    exact Or.inr (silver_perfect_antichain_polish X E hE)

end PolishSpaceBook
