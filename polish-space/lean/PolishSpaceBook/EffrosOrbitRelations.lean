module

public import PolishSpaceBook.EffrosOrbitTheorem

@[expose] public section

/-! # Borel orbit relations from Effros

The closure relation is Borel for every continuous action on a
second-countable space. Effros identifies orbit equivalence with mutual
membership in orbit closures when the orbits are nonmeager there.
The cited Polish-quotient infrastructure remains an explicit premise.
-/

namespace PolishSpaceBook
open Set Topology TopologicalSpace Filter

section ClosureRelation
variable {G X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The parameters whose orbits hit an open set form an open set. -/
theorem isOpen_orbit_hits {U : Set X} (hU : IsOpen U) :
    IsOpen {x : X | ∃ g : G, g • x ∈ U} := by
  have he : {x : X | ∃ g : G, g • x ∈ U} =
      ⋃ g : G, (fun x : X => g • x) ⁻¹' U := by
    ext x
    simp
  rw [he]
  exact isOpen_iUnion fun g => hU.preimage (by fun_prop)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    It also holds for
    actions of compact groups, because every compact-group orbit is compact and therefore closed.
-/
/-- A compact-group orbit is a compact continuous image, hence closed. -/
theorem isClosed_orbit_of_compact_group [CompactSpace G] [T2Space X] (x : X) :
    IsClosed (MulAction.orbit G x) :=
  (isCompact_range (show Continuous (fun g : G => g • x) from by fun_prop)).isClosed

omit [TopologicalSpace G] [ContinuousSMul G X] in
/-- The countable-basis formula for membership in an orbit closure. -/
theorem orbitClosureRelation_eq_iInter {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    {p : X × X | p.2 ∈ closure (MulAction.orbit G p.1)} =
      ⋂ U ∈ B, ((univ ×ˢ Uᶜ) ∪ ({x : X | ∃ g : G, g • x ∈ U} ×ˢ U)) := by
  ext p
  simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_prod, mem_univ, true_and,
    mem_compl_iff]
  rw [hB.mem_closure_iff]
  constructor
  · intro h U hUB
    by_cases hy : p.2 ∈ U
    · obtain ⟨z, hzU, hzO⟩ := h U hUB hy
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hzO
      exact Or.inr ⟨⟨g, hzU⟩, hy⟩
    · exact Or.inl hy
  · intro h U hUB hy
    rcases h U hUB with hn | ⟨⟨g, hg⟩, _⟩
    · exact (hn hy).elim
    · exact ⟨g • p.1, hg, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Let
    $$
    R:=\{(x,y):y\in\Closure{G\cdot x}\}.
    $$
    If $\{B_n\}$ is a countable basis of $X$, then $y\in\Closure{G\cdot x}$ iff, for every $n$ with $y\in B_n$, some
    $g\in G$ satisfies $g\cdot x\in B_n$. For each $n$, the set of such $x$ is open, so $R$ is Borel.
    Indeed, if
    $$
    O_n:=\{x\in X:\text{some }g\in G\text{ satisfies }g\cdot x\in B_n\},
    $$
    then each $O_n$ is open and
    $$
    R=\bigcap_n\bigl((X\times\SetDifference{X}{B_n})\cup(O_n\times B_n)\bigr).
    $$
-/
/-- The orbit-closure relation is Borel, without a nonmeagerness assumption. -/
theorem measurableSet_orbitClosureRelation [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] :
    MeasurableSet {p : X × X | p.2 ∈ closure (MulAction.orbit G p.1)} := by
  rw [orbitClosureRelation_eq_iInter (isBasis_countableBasis X)]
  apply MeasurableSet.biInter (countable_countableBasis X)
  intro U hUB
  have hU := (isBasis_countableBasis X).isOpen hUB
  exact (MeasurableSet.univ.prod hU.measurableSet.compl).union
    ((isOpen_orbit_hits (G := G) hU).measurableSet.prod hU.measurableSet)

variable [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- Orbit closures are invariant, so membership gives inclusion of closures. -/
theorem closure_orbit_subset_of_mem_closure {x y : X}
    (hy : y ∈ closure (MulAction.orbit G x)) :
    closure (MulAction.orbit G y) ⊆ closure (MulAction.orbit G x) := by
  apply closure_minimal ?_ isClosed_closure
  intro z hz
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hz
  exact (orbitClosureSubMulAction (G := G) x).smul_mem' g hy

omit [IsTopologicalGroup G] in
/-- Mutual orbit-closure membership means that the two closures coincide. -/
theorem closure_orbit_eq_of_mutual_mem {x y : X}
    (hy : y ∈ closure (MulAction.orbit G x))
    (hx : x ∈ closure (MulAction.orbit G y)) :
    closure (MulAction.orbit G x) = closure (MulAction.orbit G y) :=
  Subset.antisymm (closure_orbit_subset_of_mem_closure hx)
    (closure_orbit_subset_of_mem_closure hy)

end ClosureRelation

section Effros
variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [PolishSpace G] [TopologicalSpace X] [PolishSpace X]
  [MulAction G X] [ContinuousSMul G X]

omit [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [ContinuousSMul G X] in
/-- Two G_delta orbits with the same closure intersect because both are
comeager in that nonempty Polish closure. -/
theorem orbit_eq_of_eq_closure_of_isGdelta {x y : X}
    (hx : IsGδ (MulAction.orbit G x)) (hy : IsGδ (MulAction.orbit G y))
    (he : closure (MulAction.orbit G x) = closure (MulAction.orbit G y)) :
    MulAction.orbit G x = MulAction.orbit G y := by
  have : PolishSpace (closure (MulAction.orbit G x)) := isClosed_closure.polishSpace
  have : Nonempty (closure (MulAction.orbit G x)) :=
    ⟨⟨x, subset_closure (MulAction.mem_orbit_self x)⟩⟩
  have hxR := residual_in_closure_of_isGdelta hx
  have hyR : (Subtype.val ⁻¹' MulAction.orbit G y :
      Set (closure (MulAction.orbit G x))) ∈ residual (closure (MulAction.orbit G x)) := by
    rw [he]
    exact residual_in_closure_of_isGdelta hy
  obtain ⟨z, hzX, hzY⟩ := (dense_of_mem_residual (inter_mem hxR hyR)).nonempty
  exact (MulAction.orbit_eq_iff.mpr hzX).symm.trans (MulAction.orbit_eq_iff.mpr hzY)

omit [PolishSpace G] [IsTopologicalGroup G] in
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    We claim that
    $$
    x\mathrel{\OrbitER{G}{X}}y
    \quad\Longleftrightarrow\quad
    (x,y)\in R\text{ and }(y,x)\in R.
    $$
    The forward implication is immediate. Conversely, if $y\in\Closure{G\cdot x}$, invariance of this closed set implies
    $$\Closure{G\cdot y}\IncludedIn\Closure{G\cdot x}.$$
    The other membership condition gives the reverse inclusion, so the orbit closures are equal.
    Effros's theorem makes each orbit comeager in this common closure, because it is dense and $\Gdelta$ there. The
    two orbits therefore intersect and hence coincide. Thus $\OrbitER{G}{X}=R\cap R^{-1}$ is Borel.
-/
/-- For G_delta orbits, orbit equivalence is mutual orbit-closure membership. -/
theorem mem_orbit_iff_mutual_closure_of_isGdelta
    (hG : ∀ x : X, IsGδ (MulAction.orbit G x)) (x y : X) :
    y ∈ MulAction.orbit G x ↔
      y ∈ closure (MulAction.orbit G x) ∧ x ∈ closure (MulAction.orbit G y) := by
  constructor
  · intro h
    exact ⟨subset_closure h, subset_closure (MulAction.mem_orbit_symm.mp h)⟩
  · rintro ⟨hy, hx⟩
    have he := orbit_eq_of_eq_closure_of_isGdelta (hG x) (hG y)
      (closure_orbit_eq_of_mutual_mem hy hx)
    rw [he]
    exact MulAction.mem_orbit_self y

omit [PolishSpace G] [IsTopologicalGroup G] in
/-- The closure-relation formula makes the orbit relation Borel when all
orbits are G_delta. -/
theorem measurableSet_orbitRelation_of_isGdelta
    [MeasurableSpace X] [BorelSpace X]
    (hG : ∀ x : X, IsGδ (MulAction.orbit G x)) :
    MeasurableSet {p : X × X | p.2 ∈ MulAction.orbit G p.1} := by
  have he : {p : X × X | p.2 ∈ MulAction.orbit G p.1} =
      {p : X × X | p.2 ∈ closure (MulAction.orbit G p.1)} ∩
        Prod.swap ⁻¹' {p : X × X | p.2 ∈ closure (MulAction.orbit G p.1)} := by
    ext p
    exact mem_orbit_iff_mutual_closure_of_isGdelta hG p.1 p.2
  rw [he]
  exact measurableSet_orbitClosureRelation.inter
    (measurableSet_orbitClosureRelation.preimage measurable_swap)

omit [PolishSpace G] [IsTopologicalGroup G] in
/-- Closed orbits satisfy the Borel-relation conclusion directly. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The hypothesis is automatic for closed orbits,
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    In these settings every
    orbit is at most $\bPi^0_2$ in its closure, and the orbit relation is Borel rather than properly analytic.
-/
theorem measurableSet_orbitRelation_of_closed
    [MeasurableSpace X] [BorelSpace X]
    (hC : ∀ x : X, IsClosed (MulAction.orbit G x)) :
    MeasurableSet {p : X × X | p.2 ∈ MulAction.orbit G p.1} :=
  measurableSet_orbitRelation_of_isGdelta (fun x => (hC x).isGδ)

omit [PolishSpace G] [IsTopologicalGroup G] in
/-- Compact-group actions have Borel orbit relations because their orbits
are closed. No Polish-quotient premise is needed for this special case. -/
theorem measurableSet_orbitRelation_of_compact_group
    [CompactSpace G] [MeasurableSpace X] [BorelSpace X] :
    MeasurableSet {p : X × X | p.2 ∈ MulAction.orbit G p.1} :=
  measurableSet_orbitRelation_of_closed (isClosed_orbit_of_compact_group (G := G))

/-- Effros's Borel-relation corollary. The quotient hypotheses are precisely
the external Polish-quotient infrastructure cited in the chapter. -/
theorem measurableSet_orbitRelation_of_nonmeagre
    [MeasurableSpace X] [BorelSpace X]
    (hQ : ∀ x : X, PolishSpace (G ⧸ MulAction.stabilizer G x))
    (hN : ∀ x : X, ¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x)))) :
    MeasurableSet {p : X × X | p.2 ∈ MulAction.orbit G p.1} := by
  apply measurableSet_orbitRelation_of_isGdelta
  intro x
  have := hQ x
  exact (effros_nonmeagre_iff_isGdelta x).mp (hN x)

end Effros


end PolishSpaceBook
