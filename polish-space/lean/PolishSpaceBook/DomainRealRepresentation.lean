module

public import PolishSpaceBook.DomainRepresentations
public import PolishSpaceBook.DomainIntervalBasis

@[expose] public section

namespace PolishSpaceBook
open Set Function Topology

/-- Transport the values of a representation along a homeomorphism. -/
def Representation.domainHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (δ : Representation X) (e : X ≃ₜ Y) : Representation Y where
  domain := δ.domain
  toFun := e ∘ δ.toFun
  surjective := e.surjective.comp δ.surjective

theorem Representation.domainHomeomorph_admissible {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {δ : Representation X}
    (hδ : δ.IsAdmissible) (e : X ≃ₜ Y) : (δ.domainHomeomorph e).IsAdmissible := by
  apply (admissible_iff_partial_lifting _).mpr
  refine ⟨e.continuous.comp hδ.1, ?_⟩
  intro E g hg
  obtain ⟨f, hf, heq⟩ := (admissible_iff_partial_lifting δ).mp hδ |>.2 E
    (e.symm ∘ g) (e.symm.continuous.comp hg)
  refine ⟨f, hf, fun p => ?_⟩
  change e (δ.toFun (f p)) = g p
  rw [heq p]
  exact e.apply_symm_apply (g p)

theorem interval_basis_enumerable :
    ∃ b : ℕ → IntervalInformation, rationalIntervalBasis = range b :=
  interval_countable_basis.1.exists_eq_range
    (((interval_countable_basis.2) ⊥).1.mono inter_subset_left)

noncomputable def intervalBasisEnumeration : ℕ → IntervalInformation :=
  Classical.choose interval_basis_enumerable

theorem intervalBasisEnumeration_range : range intervalBasisEnumeration = rationalIntervalBasis :=
  (Classical.choose_spec interval_basis_enumerable).symm

theorem intervalBasisEnumeration_isBasis : IsDomainBasis (range intervalBasisEnumeration) := by
  rw [intervalBasisEnumeration_range]
  exact interval_countable_basis.2

section Scott
local instance : TopologicalSpace IntervalInformation := Topology.scott IntervalInformation univ
local instance : Topology.IsScott IntervalInformation univ := ⟨rfl⟩

/-- Names are way-below rational interval chains whose supremum is maximal;
their values are the real numbers identified with these singleton intervals. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Computationally, an element $[a, b] \in \IntervalDomain$ represents "the real $x$ is known to within precision
    $|b-a|$."
    A directed family $[a_n, b_n]$ refining toward $[x, x]$ is the domain-theoretic analogue of a
    \termuse{Cauchy name}. The maximal-element presentation induced by $\IntervalDomain$ gives a domain model of $\R$.
    To obtain names in the sense of TTE, use countable rational-interval chains converging to a singleton.
    Their supremum map gives a representation equivalent to the \termuse{Cauchy representation}, as explained below.
-/
noncomputable def realIntervalChainRepresentation : Representation ℝ :=
  (domainRepresentation intervalBasisEnumeration intervalBasisEnumeration_isBasis
    {I : IntervalInformation | IsMax I}).domainHomeomorph intervalMaximalHomeomorph.symm

/-- Decoding recovers the same singleton supremum of the supplied rational interval chain. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Computationally, an element $[a, b] \in \IntervalDomain$ represents "the real $x$ is known to within precision
    $|b-a|$."
    A directed family $[a_n, b_n]$ refining toward $[x, x]$ is the domain-theoretic analogue of a
    \termuse{Cauchy name}. The maximal-element presentation induced by $\IntervalDomain$ gives a domain model of $\R$.
    To obtain names in the sense of TTE, use countable rational-interval chains converging to a singleton.
    Their supremum map gives a representation equivalent to the \termuse{Cauchy representation}, as explained below.
-/
theorem realIntervalChainRepresentation_singleton (p : realIntervalChainRepresentation.domain) :
    intervalSingleton (realIntervalChainRepresentation.toFun p) =
      basisNameSup intervalBasisEnumeration
        (restrictedBasisChain intervalBasisEnumeration {I : IntervalInformation | IsMax I} p) := by
  change intervalSingleton (intervalMaximalHomeomorph.symm
    (restrictedBasisValue intervalBasisEnumeration {I : IntervalInformation | IsMax I} p)) = _
  rw [← intervalMaximalHomeomorph_apply]
  exact congrArg Subtype.val (intervalMaximalHomeomorph.apply_symm_apply _)

theorem realIntervalChainRepresentation_admissible :
    realIntervalChainRepresentation.IsAdmissible :=
  Representation.domainHomeomorph_admissible
    (domainRepresentation_isAdmissible intervalBasisEnumeration intervalBasisEnumeration_isBasis
      {I : IntervalInformation | IsMax I}) intervalMaximalHomeomorph.symm

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Computationally, an element $[a, b] \in \IntervalDomain$ represents "the real $x$ is known to within precision
    $|b-a|$."
    A directed family $[a_n, b_n]$ refining toward $[x, x]$ is the domain-theoretic analogue of a
    \termuse{Cauchy name}. The maximal-element presentation induced by $\IntervalDomain$ gives a domain model of $\R$.
    To obtain names in the sense of TTE, use countable rational-interval chains converging to a singleton.
    Their supremum map gives a representation equivalent to the \termuse{Cauchy representation}, as explained below.
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Thus domain chains and TTE names are alternative presentations of the same approximation process. The
    $\IntervalDomain$ presentation corresponds to the standard Cauchy representation of $\R$.
-/
theorem realIntervalChainRepresentation_cauchy_equivalent (q : ℕ → ℝ) (hq : DenseRange q) :
    ContinuouslyEquivalent realIntervalChainRepresentation (cauchyRepresentationObject q hq) :=
  continuouslyEquivalent_of_admissible realIntervalChainRepresentation_admissible
    (cauchyRepresentationObject_isAdmissible q hq)

end Scott
end PolishSpaceBook
