module

public import PolishSpaceBook.EffrosOrbitMaps
public import PolishSpaceBook.PolishSpaces

@[expose] public section

/-! # The remaining implications of Effros's theorem

The book cites the Polish-quotient theorem as external infrastructure.
Where it is needed, the hypothesis `PolishSpace (G ⧸ stabilizer G x)`
is explicit; the proofs below do not assert a new quotient theorem.
-/

namespace PolishSpaceBook
open Set Topology TopologicalSpace Filter

section Subspaces
variable {X : Type*} [TopologicalSpace X] [PolishSpace X]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \emph{(2) $\Leftrightarrow$ (3).} Put $Y:=\Closure{G\cdot x}$. Since $Y$ is closed in the metrizable space $X$,
    it is $\Gdelta$ in $X$.
    Every relatively open subset of $Y$ is the intersection of $Y$ with an open subset of $X$.
    Consequently, a subset of $Y$ is $\Gdelta$ in $Y$ if and only if it is $\Gdelta$ in $X$.
-/
/-- A subset of a closed subspace is G_delta there exactly when it is
G_delta in the ambient Polish space. -/
theorem isGdelta_in_closed_iff {A S : Set X} (hS : IsClosed S) (hAS : A ⊆ S) :
    IsGδ (Subtype.val ⁻¹' A : Set S) ↔ IsGδ A := by
  constructor
  · intro h
    obtain ⟨U, hU, he⟩ := h.eq_iInter_nat
    choose V hV hVU using fun n => isOpen_induced_iff.mp (hU n)
    have ha : A = S ∩ ⋂ n, V n := by
      ext x
      constructor
      · intro hx
        refine ⟨hAS hx, mem_iInter.mpr fun n => ?_⟩
        have hu : (⟨x, hAS hx⟩ : S) ∈ U n := by
          have ht : (⟨x, hAS hx⟩ : S) ∈ ⋂ n, U n := he ▸ hx
          exact mem_iInter.mp ht n
        rwa [← hVU n] at hu
      · rintro ⟨hxS, hxV⟩
        have ht : (⟨x, hxS⟩ : S) ∈ ⋂ n, U n := by
          apply mem_iInter.mpr
          intro n
          rw [← hVU n]
          exact mem_iInter.mp hxV n
        rwa [← he] at ht
    rw [ha]
    exact hS.isGδ.inter (IsGδ.iInter_of_isOpen hV)
  · exact fun h => h.preimage continuous_subtype_val

omit [PolishSpace X] in
/-- Every set is dense when viewed as a subset of its own closure. -/
theorem dense_in_closure (A : Set X) :
    Dense (Subtype.val ⁻¹' A : Set (closure A)) := by
  intro x
  rw [closure_subtype]
  have he : Subtype.val '' (Subtype.val ⁻¹' A : Set (closure A)) = A :=
    Set.image_preimage_eq_inter_range.trans (by
      rw [Subtype.range_coe_subtype]
      exact inter_eq_left.mpr subset_closure)
  rw [he]
  exact x.property

omit [PolishSpace X] in
/-- A G_delta set is comeager in its closure. -/
theorem residual_in_closure_of_isGdelta {A : Set X} (hA : IsGδ A) :
    (Subtype.val ⁻¹' A : Set (closure A)) ∈ residual (closure A) := by
  obtain ⟨U, hU, he⟩ := (hA.preimage continuous_subtype_val).eq_iInter_nat
  have hd : ∀ n, Dense (U n) := by
    intro n
    apply (dense_in_closure A).mono
    rw [he]
    exact iInter_subset U n
  have hm : IsMeagre (⋃ n, (U n)ᶜ) := by
    apply isMeagre_iUnion
    intro n
    have hn : IsNowhereDense (U n)ᶜ :=
      (isClosed_isNowhereDense_iff_compl.mpr
        (by simpa only [compl_compl] using And.intro (hU n) (hd n))).2
    exact hn.isMeagre
  simpa only [IsMeagre, compl_iUnion, compl_compl, ← he] using hm

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \emph{(3) $\Rightarrow$ (1).} The orbit $G\cdot x$ is dense in $Y$ by definition of closure.
    Write $G\cdot x=\bigcap_n U_n$, where each $U_n$ is open in $Y$. Every $U_n$ is dense in $Y$, so
    $$\SetDifference{Y}{(G\cdot x)}=\bigcup_n\SetDifference{Y}{U_n}$$
    is meager in $Y$. Thus the orbit is comeager there. Since the nonempty Polish space $Y$ is a Baire space,
    the orbit cannot also be meager.
-/
/-- A nonempty G_delta set is nonmeager in its closure. -/
theorem not_isMeagre_in_closure_of_isGdelta {A : Set X}
    (hA : IsGδ A) (hn : A.Nonempty) :
    ¬ IsMeagre (Subtype.val ⁻¹' A : Set (closure A)) := by
  have : PolishSpace (closure A) := isClosed_closure.polishSpace
  have : Nonempty (closure A) := ⟨⟨hn.choose, subset_closure hn.choose_spec⟩⟩
  intro hm
  have hc : IsMeagre (Subtype.val ⁻¹' A : Set (closure A))ᶜ := by
    simpa only [IsMeagre, compl_compl] using residual_in_closure_of_isGdelta hA
  have hu : IsMeagre (univ : Set (closure A)) := by
    simpa only [union_compl_self] using hm.union hc
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hu

end Subspaces

section Orbits
variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [PolishSpace G] [TopologicalSpace X] [PolishSpace X]
  [MulAction G X] [ContinuousSMul G X]

omit [IsTopologicalGroup G] [PolishSpace G] [ContinuousSMul G X] in
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \emph{(4) $\Rightarrow$ (2).} If $\pi_x$ is a homeomorphism, $G \cdot x$ is Polish in the subspace topology from
    $X$,
    hence $\Gdelta$ in $X$ by Alexandrov's theorem in §{sec:alexandrov-theorem}.
-/
/-- Alexandrov's theorem supplies the implication from the canonical
homeomorphism to a G_delta orbit. The quotient is Polish by the external
closed-subgroup quotient theorem cited in the book. -/
theorem isGdelta_orbit_of_quotient_homeomorph (x : X)
    [PolishSpace (G ⧸ MulAction.stabilizer G x)]
    (h : IsHomeomorph (MulAction.orbitEquivQuotientStabilizer G x).symm) :
    IsGδ (MulAction.orbit G x) := by
  have : PolishSpace (MulAction.orbit G x) :=
    (h.homeomorph _).symm.isClosedEmbedding.polishSpace
  exact alexandrov_theorem.mp inferInstance

/-- Effros's nonmeager/G_delta equivalence, with the cited quotient
infrastructure recorded explicitly. -/
theorem effros_nonmeagre_iff_isGdelta (x : X)
    [PolishSpace (G ⧸ MulAction.stabilizer G x)] :
    (¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x)))) ↔
      IsGδ (MulAction.orbit G x) := by
  constructor
  · intro h
    exact isGdelta_orbit_of_quotient_homeomorph x
      (quotientStabilizerOrbitHomeomorph x h).isHomeomorph
  · intro h
    exact not_isMeagre_in_closure_of_isGdelta h ⟨x, MulAction.mem_orbit_self x⟩

/-- The fourth condition of Effros is the homeomorphism property of the
canonical map, not merely existence of some homeomorphism. -/
theorem effros_isGdelta_iff_quotient_homeomorph (x : X)
    [PolishSpace (G ⧸ MulAction.stabilizer G x)] :
    IsGδ (MulAction.orbit G x) ↔
      IsHomeomorph (MulAction.orbitEquivQuotientStabilizer G x).symm := by
  constructor
  · intro h
    exact (quotientStabilizerOrbitHomeomorph x
      ((effros_nonmeagre_iff_isGdelta x).mpr h)).isHomeomorph
  · exact isGdelta_orbit_of_quotient_homeomorph x

end Orbits
end PolishSpaceBook
