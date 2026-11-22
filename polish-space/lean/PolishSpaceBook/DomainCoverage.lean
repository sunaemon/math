module

public import PolishSpaceBook.DomainScottTopology
public import PolishSpaceBook.DomainIntervalBasis
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PolishSpaceBook
open Set Topology

/-- Domain-theoretic directedness includes nonemptiness. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A subset $S\IncludedIn D$ of a poset $(D,\sqsubseteq)$ is \termdefine{directed} if it is nonempty and every finite
    subset
    has an upper bound in $S$; equivalently, $S$ is nonempty and for every $s,t\in S$ there is $u\in S$ with
    $s\sqsubseteq u$ and $t\sqsubseteq
    u$. A \termdefine{directed-complete partial order} (dcpo) is a poset in which every directed subset $S$ has a supremum,
    written
    $$\DirectedSup S.$$
    This is the standard domain-theoretic notation for directed suprema, not a disjoint-union notation. The supremum is the
    idealized result of accumulating all finite information in $S$.
-/
def DomainDirected {D : Type*} [Preorder D] (S : Set D) : Prop :=
  S.Nonempty ∧ DirectedOn (· ≤ ·) S

/-- The book's dcpos need not have bottom. Mathlib's `CompletePartialOrder`
additionally supplies bottom and a chosen supremum, including for the empty set. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A subset $S\IncludedIn D$ of a poset $(D,\sqsubseteq)$ is \termdefine{directed} if it is nonempty and every finite
    subset
    has an upper bound in $S$; equivalently, $S$ is nonempty and for every $s,t\in S$ there is $u\in S$ with
    $s\sqsubseteq u$ and $t\sqsubseteq
    u$. A \termdefine{directed-complete partial order} (dcpo) is a poset in which every directed subset $S$ has a supremum,
    written
    $$\DirectedSup S.$$
    This is the standard domain-theoretic notation for directed suprema, not a disjoint-union notation. The supremum is the
    idealized result of accumulating all finite information in $S$.
-/
def IsDomainDcpo (D : Type*) [PartialOrder D] : Prop :=
  ∀ S : Set D, DomainDirected S → ∃ s, IsLUB S s

theorem isDomainDcpo_of_completePartialOrder (D : Type*) [CompletePartialOrder D] :
    IsDomainDcpo D := fun _ h => ⟨_, h.2.isLUB_sSup⟩

/-- Pairwise directedness is equivalent to upper bounds for every finite observation family. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A subset $S\IncludedIn D$ of a poset $(D,\sqsubseteq)$ is \termdefine{directed} if it is nonempty and every finite
    subset
    has an upper bound in $S$; equivalently, $S$ is nonempty and for every $s,t\in S$ there is $u\in S$ with
    $s\sqsubseteq u$ and $t\sqsubseteq
    u$. A \termdefine{directed-complete partial order} (dcpo) is a poset in which every directed subset $S$ has a supremum,
    written
    $$\DirectedSup S.$$
    This is the standard domain-theoretic notation for directed suprema, not a disjoint-union notation. The supremum is the
    idealized result of accumulating all finite information in $S$.
-/
theorem domainDirected_iff_finite_upperBounds {D : Type*} [Preorder D] (S : Set D) :
    DomainDirected S ↔ S.Nonempty ∧
      ∀ t : Finset D, (↑t : Set D) ⊆ S → ∃ u ∈ S, ∀ a ∈ t, a ≤ u := by
  classical
  constructor
  · rintro ⟨hne, hd⟩
    refine ⟨hne, ?_⟩
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, hu, by simp⟩
    | @insert a t _ ih =>
      intro ht
      obtain ⟨u, hu, hub⟩ := ih (fun _ hb => ht (Finset.mem_insert_of_mem hb))
      obtain ⟨v, hv, hav, huv⟩ := hd a (ht (Finset.mem_insert_self _ _)) u hu
      refine ⟨v, hv, fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hav
      · exact (hub b hb).trans huv
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun a ha b hb => ?_⟩
    obtain ⟨u, hu, hub⟩ := h {a, b} (by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ha
      · exact Finset.mem_singleton.mp hc ▸ hb)
    exact ⟨u, hu, hub a (by simp), hub b (by simp)⟩

/-- A continuous domain includes directed completeness as well as approximation. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A dcpo $D$ is \termdefineas{continuous dcpo}{continuous} if, for every $b\in D$, the set
    $$\{a\in D:a\ll b\}$$
    is directed and has supremum $b$. It is \termdefineas{omega-continuous}{$\omega$-continuous} if there is a countable
    subset $B\IncludedIn D$ such that, for every $b\in D$, the set $\{a\in B:a\ll b\}$ is directed with supremum $b$. Such a
    $B$ is a \termdefineas{domain-theoretic basis}{basis}. In this chapter, a \termdefineas{domain-theoretic domain}{domain}
    means a continuous dcpo, and an \termdefineas{omega-continuous domain}{$\omega$-continuous domain} means a continuous
    dcpo with a countable basis.
-/
def IsContinuousDomain (D : Type*) [PartialOrder D] : Prop :=
  IsDomainDcpo D ∧ IsDomainBasis (Set.univ : Set D)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A dcpo $D$ is \termdefineas{continuous dcpo}{continuous} if, for every $b\in D$, the set
    $$\{a\in D:a\ll b\}$$
    is directed and has supremum $b$. It is \termdefineas{omega-continuous}{$\omega$-continuous} if there is a countable
    subset $B\IncludedIn D$ such that, for every $b\in D$, the set $\{a\in B:a\ll b\}$ is directed with supremum $b$. Such a
    $B$ is a \termdefineas{domain-theoretic basis}{basis}. In this chapter, a \termdefineas{domain-theoretic domain}{domain}
    means a continuous dcpo, and an \termdefineas{omega-continuous domain}{$\omega$-continuous domain} means a continuous
    dcpo with a countable basis.
-/
def IsOmegaContinuousDomain (D : Type*) [PartialOrder D] : Prop :=
  IsDomainDcpo D ∧ ∃ B : Set D, B.Countable ∧ IsDomainBasis B

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A dcpo $D$ is \termdefineas{continuous dcpo}{continuous} if, for every $b\in D$, the set
    $$\{a\in D:a\ll b\}$$
    is directed and has supremum $b$. It is \termdefineas{omega-continuous}{$\omega$-continuous} if there is a countable
    subset $B\IncludedIn D$ such that, for every $b\in D$, the set $\{a\in B:a\ll b\}$ is directed with supremum $b$. Such a
    $B$ is a \termdefineas{domain-theoretic basis}{basis}. In this chapter, a \termdefineas{domain-theoretic domain}{domain}
    means a continuous dcpo, and an \termdefineas{omega-continuous domain}{$\omega$-continuous domain} means a continuous
    dcpo with a countable basis.
-/
theorem IsOmegaContinuousDomain.continuous {D : Type*} [PartialOrder D]
    (h : IsOmegaContinuousDomain D) : IsContinuousDomain D := by
  obtain ⟨hd, B, _, hB⟩ := h
  exact ⟨hd, fun x => by simpa only [univ_inter] using hB.continuous x⟩

/-- Canonical Scott continuity is exactly monotonicity and preservation of directed LUBs. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A function $f:D\to E$ between dcpos is \termdefine{Scott-continuous} if it is monotone and preserves directed suprema:
    $$
    f(\DirectedSup S)=\DirectedSup f[S]
    \qquad(S\IncludedIn D\text{ directed}).
    $$
-/
theorem domain_scottContinuous_iff_monotone_lub {D E : Type*} [Preorder D] [Preorder E]
    (f : D → E) : ScottContinuous f ↔ Monotone f ∧
      ∀ (S : Set D) (s : D), DomainDirected S → IsLUB S s → IsLUB (f '' S) (f s) := by
  exact ⟨fun hf => ⟨hf.monotone, fun _ _ hd hs => hf hd.1 hd.2 hs⟩,
    fun h _ hne hd _ hs => h.2 _ _ ⟨hne, hd⟩ hs⟩

section ScottSeparation
variable {D : Type*} [PartialOrder D] [TopologicalSpace D] [Topology.IsScott D univ]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    *   *Open sets are finitely observable properties.* If a directed supremum has a Scott-open property,
        some member of the directed family already has that property. This is a topological condition; no effective
        enumeration of observations is part of its definition.
-/
theorem domain_scott_observable {U S : Set D} {s : D} (hU : IsOpen U)
    (hS : DomainDirected S) (hs : IsLUB S s) (hmem : s ∈ U) :
    ∃ x ∈ S, x ∈ U := by
  obtain ⟨x, hx, hxu⟩ := (domain_scott_open_iff U).mp hU |>.2 hS.1 hS.2 hs hmem
  exact ⟨x, hx, hxu⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Scott topologies are $T_0$. For a nontrivial dcpo with a least element, $\bot$ lies in the closure of every nonempty
    subset. Such a space is not $T_1$, and hence is not Hausdorff.
-/
theorem domain_scott_t0 : T0Space D := inferInstance

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Scott topologies are $T_0$. For a nontrivial dcpo with a least element, $\bot$ lies in the closure of every nonempty
    subset. Such a space is not $T_1$, and hence is not Hausdorff.
-/
theorem domain_scott_not_t1 [OrderBot D] [Nontrivial D] : ¬ T1Space D := by
  intro h
  let : T1Space D := h
  obtain ⟨a, ha⟩ := exists_ne (⊥ : D)
  have hc : (⊥ : D) ∈ closure ({a} : Set D) := domain_bot_mem_closure (singleton_nonempty a)
  rw [isClosed_singleton.closure_eq] at hc
  exact ha (mem_singleton_iff.mp hc).symm

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Scott topologies are $T_0$. For a nontrivial dcpo with a least element, $\bot$ lies in the closure of every nonempty
    subset. Such a space is not $T_1$, and hence is not Hausdorff.
-/
theorem domain_scott_not_t2 [OrderBot D] [Nontrivial D] : ¬ T2Space D := by
  intro h
  let : T2Space D := h
  exact domain_scott_not_t1 (D := D) inferInstance

/-- Maximal points have no nontrivial specialization in their relative Scott topology. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The word "designated" matters. The points of $X$ need not be the maximal elements of $D$: every maximal-point subspace
    is $T_1$
-/
theorem domain_maximal_t1 : T1Space {x : D // IsMax x} := by
  apply t1Space_iff_specializes_imp_eq.mpr
  intro x y h
  have hle : y.val ≤ x.val :=
    (domain_scott_specializes_iff x.val y.val).mp (h.map continuous_subtype_val)
  exact Subtype.ext (le_antisymm (y.property hle) hle)

end ScottSeparation

section LinearScott
variable {L : Type*} [LinearOrder L] [TopologicalSpace L] [Topology.IsScott L univ]

/-- Comparability prevents a Scott chain from containing a nontrivial T₁ subspace. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    subspace homeomorphic to Cantor space: any two distinct points are comparable in the specialization order,
    so no subspace with two or more points is $T_1$. Thus the Cantor-subspace conclusion of the classical perfect
    set theorem does not transfer unchanged.
-/
theorem linear_scott_t1_subspace_subsingleton (S : Set L) [T1Space S] : Subsingleton S := by
  refine ⟨fun x y => ?_⟩
  rcases le_total x.val y.val with h | h
  · exact ((subtype_specializes_iff y x).mpr
      ((domain_scott_specializes_iff y.val x.val).mpr h)).eq.symm
  · exact ((subtype_specializes_iff x y).mpr
      ((domain_scott_specializes_iff x.val y.val).mpr h)).eq

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    subspace homeomorphic to Cantor space: any two distinct points are comparable in the specialization order,
    so no subspace with two or more points is $T_1$. Thus the Cantor-subspace conclusion of the classical perfect
    set theorem does not transfer unchanged.
-/
theorem linear_scott_no_homeomorph_t1 (S : Set L) (Y : Type*)
    [TopologicalSpace Y] [T1Space Y] [Nontrivial Y] : ¬ Nonempty (Y ≃ₜ S) := by
  rintro ⟨h⟩
  let : T1Space S := h.t1Space
  let : Subsingleton S := linear_scott_t1_subspace_subsingleton S
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Y
  exact hxy (h.injective (Subsingleton.elim _ _))

end LinearScott

/-- The concrete interval order is directed complete and has the actual rational basis. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    *   $\IntervalDomain$ is an $\omega$-continuous dcpo with countable basis
        $\{\bot\}\cup\{[a, b] : a, b \in \QQ,\ a\le b\}$
-/
theorem interval_omegaContinuousDomain : IsOmegaContinuousDomain IntervalInformation :=
  ⟨isDomainDcpo_of_completePartialOrder _, rationalIntervalBasis,
    interval_countable_basis.1, interval_countable_basis.2⟩

end PolishSpaceBook
