module

public import PolishSpaceBook.CategoryLocalization
public import PolishSpaceBook.SuslinBaireProperty
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

/-! # The category argument for open orbit maps

The ambient version is applied to the invariant closure of an orbit.
The countable-translate argument and the two intersecting local orbit pieces
follow the proof of Effros's theorem in the book.
-/

namespace PolishSpaceBook
open Set Topology TopologicalSpace Filter
open scoped Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Every nonempty open group piece of a nonmeager orbit is nonmeager. -/
theorem not_isMeagre_open_orbit_image [SeparableSpace G] (x : X)
    (hx : ¬ IsMeagre (MulAction.orbit G x))
    {W : Set G} (hW : IsOpen W) (hn : W.Nonempty) :
    ¬ IsMeagre ((fun g : G => g • x) '' W) := by
  obtain ⟨d, hd⟩ := exists_dense_seq G
  intro hm
  have ht (n : ℕ) :
      IsMeagre ((Homeomorph.smul (d n)) '' ((fun g : G => g • x) '' W)) :=
    (Homeomorph.smul (d n)).isEmbedding.isInducing.isMeagre_image hm
  apply hx
  apply (isMeagre_iUnion ht).mono
  intro y hy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  have ho : IsOpen {r : G | r⁻¹ * g ∈ W} :=
    hW.preimage (continuous_inv.mul continuous_const)
  obtain ⟨w, hw⟩ := hn
  have hne : ({r : G | r⁻¹ * g ∈ W} : Set G).Nonempty :=
    ⟨g * w⁻¹, by simpa using hw⟩
  obtain ⟨n, hdn⟩ := hd.exists_mem_open ho hne
  refine mem_iUnion.mpr ⟨n, ?_⟩
  refine ⟨(d n)⁻¹ • (g • x), ?_, by simp⟩
  exact ⟨(d n)⁻¹ * g, hdn, by simp [mul_smul]⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof of the lemma] Choose a symmetric open $W\ni e$ with $W^{-1}W\IncludedIn V$. We first show that
    $W\cdot
    x$ is non-meager in $Y$. Let $\{g_n:n\in\omega\}$ be a countable dense subset of $G$. Since $\bigcup_n g_nW=G$, we
    have
    $$G\cdot x=\bigcup_n g_nW\cdot x.$$
    If every $g_nW\cdot x$ were meager in $Y$, the orbit would be meager, contrary to the hypothesis. Thus some
    $g_nW\cdot
    x$ is non-meager. Applying the homeomorphism $g_n^{-1}:Y\to Y$ shows that $W\cdot x$ is non-meager.

    The set $W\cdot x$ is analytic, hence has the Baire property by §{sec:regularity-independence}. Baire-property
    localization therefore gives a nonempty relatively open $\Omega\IncludedIn Y$ such that $W\cdot x$ is comeager in
    $\Omega$. Pick $k\in W$ with $k\cdot x\in\Omega$, and set
    $$O:=k^{-1}\Omega.$$
    Then $O$ is a relatively open neighborhood of $x$ in $Y$.

    We claim that
    $$O\cap(G\cdot x)\IncludedIn W^{-1}W\cdot x\IncludedIn V\cdot x.$$
    Let $y\in O\cap(G\cdot x)$ and put
    $$H:=W\cap\{h\in G:h\cdot y\in\Omega\}.$$
    Continuity of the action makes $H$ open. Since $k\in W$ and $k\cdot y\in\Omega$, it contains $k$, and by definition
    $$H\cdot y\IncludedIn\Omega.$$
    The set $H\cdot y$ is non-meager in $Y$: if $\{r_n\}$ is dense in $G$, then $\bigcup_n r_nH\cdot y=G\cdot y=G\cdot
    x$,
    and otherwise the non-meager orbit would be a countable union of meager sets.

    Thus $H\cdot y$ is non-meager in $\Omega$, while $W\cdot x$ is comeager there. Their
    intersection is nonempty. Choose $h\in H$ and $w\in W$ with
    $$h\cdot y=w\cdot x.$$
    Then
    $$y=h^{-1}w\cdot x\in W^{-1}W\cdot x\IncludedIn V\cdot x.$$
    This proves the claim and hence the lemma.
    \end{proof}
-/
/-- The local Pettis argument, in any Polish ambient space where the orbit
is nonmeager. Restriction to the orbit closure gives Effros's hypothesis. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[Pettis lemma for orbit maps]
-/
theorem exists_open_orbit_neighborhood [PolishSpace G] [PolishSpace X]
    (x : X) (hx : ¬ IsMeagre (MulAction.orbit G x))
    {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      O ∩ MulAction.orbit G x ⊆ (fun g : G => g • x) '' V := by
  obtain ⟨D, hD, h1D, hDD⟩ := exists_open_nhds_one_mul_subset (hV.mem_nhds h1)
  let W : Set G := D ∩ Inv.inv ⁻¹' D
  have hW : IsOpen W := hD.inter (hD.preimage continuous_inv)
  have h1W : (1 : G) ∈ W := ⟨h1D, by simpa using h1D⟩
  have hWW {h w : G} (hh : h ∈ W) (hw : w ∈ W) : h⁻¹ * w ∈ V :=
    hDD (Set.mul_mem_mul hh.2 hw.1)
  let A : Set X := (fun g : G => g • x) '' W
  have hAn : ¬ IsMeagre A := not_isMeagre_open_orbit_image x hx hW ⟨1, h1W⟩
  have hAb : BaireMeasurableSet A := by
    borelize G
    borelize X
    exact analyticSet_baireMeasurableSet A
      (analyticSet_image_of_borel hW.measurableSet
        (show Continuous (fun g : G => g • x) from by fun_prop).measurable)
  obtain ⟨Ω, hΩ, hΩn, _, hΩA⟩ :=
    baire_localization_ambient hAb isOpen_univ (by simpa using hAn)
  have hn : (A ∩ Ω).Nonempty :=
    nonempty_of_not_isMeagre (not_isMeagre_inter_of_comeagre hΩ hΩn subset_rfl hΩA)
  obtain ⟨z, ⟨⟨k, hkW, rfl⟩, hkΩ⟩⟩ := hn
  refine ⟨(fun y : X => k • y) ⁻¹' Ω, hΩ.preimage (by fun_prop), hkΩ, ?_⟩
  rintro y ⟨hyO, hyOrb⟩
  let H : Set G := W ∩ (fun h : G => h • y) ⁻¹' Ω
  have hH : IsOpen H := hW.inter (hΩ.preimage (by fun_prop))
  have hkH : k ∈ H := ⟨hkW, hyO⟩
  have hy : ¬ IsMeagre (MulAction.orbit G y) := by
    rwa [MulAction.orbit_eq_iff.mpr hyOrb]
  have hHn := not_isMeagre_open_orbit_image y hy hH ⟨k, hkH⟩
  have hi : (((fun h : G => h • y) '' H) ∩ A).Nonempty := by
    by_contra he
    apply hHn
    apply hΩA.mono
    rintro z ⟨h, hh, rfl⟩
    exact ⟨hh.2, fun hz => he ⟨h • y, ⟨h, hh, rfl⟩, hz⟩⟩
  obtain ⟨z, ⟨h, hh, he⟩, w, hw, we⟩ := hi
  dsimp only at he we
  refine ⟨h⁻¹ * w, hWW hh.1 hw, ?_⟩
  change (h⁻¹ * w) • x = y
  rw [mul_smul, we, ← he]
  simp

/-- The local orbit neighborhoods make the orbit map open into its range. -/
theorem isOpenMap_orbitMap_of_nonmeagre [PolishSpace G] [PolishSpace X]
    (x : X) (hx : ¬ IsMeagre (MulAction.orbit G x)) :
    IsOpenMap (fun g : G =>
      (⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩ : MulAction.orbit G x)) := by
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨h, hh, rfl⟩
  let V : Set G := (fun g : G => h * g) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ V := by simpa [V] using hh
  obtain ⟨O, hO, hxO, hOV⟩ := exists_open_orbit_neighborhood x hx hV h1
  refine ⟨(fun y : MulAction.orbit G x => h⁻¹ • (y : X)) ⁻¹' O, ?_,
    hO.preimage (by fun_prop), by simpa using hxO⟩
  intro y hy
  have hyOrb : h⁻¹ • (y : X) ∈ MulAction.orbit G x := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.property
    exact MulAction.mem_orbit_iff.mpr ⟨h⁻¹ * g, by simp [mul_smul, hg]⟩
  obtain ⟨v, hv, he⟩ := hOV ⟨hy, hyOrb⟩
  dsimp only at he
  refine ⟨h * v, hv, ?_⟩
  apply Subtype.ext
  change (h * v) • x = (y : X)
  rw [mul_smul, he]
  simp

/-- The orbit closure is invariant under the group action. -/
def orbitClosureSubMulAction (x : X) : SubMulAction G X where
  carrier := closure (MulAction.orbit G x)
  smul_mem' g {y} hy := by
    have he : g • closure (MulAction.orbit G x) = closure (MulAction.orbit G x) := by
      rw [← closure_smul, MulAction.smul_orbit]
    rw [← he]
    exact ⟨_, hy, rfl⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    \emph{(1) $\Rightarrow$ (4).} It suffices to show that $\pi_x$ is open onto its image. We use the following orbit form
    of Pettis's lemma.
-/
/-- Effros's central implication, with meagerness measured in the orbit closure. -/
theorem isOpenMap_orbitMap_of_nonmeagre_in_closure [PolishSpace G] [PolishSpace X]
    (x : X)
    (hx : ¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x)))) :
    IsOpenMap (fun g : G =>
      (⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩ : MulAction.orbit G x)) := by
  let Y := orbitClosureSubMulAction (G := G) x
  let xY : Y := ⟨x, subset_closure (MulAction.mem_orbit_self x)⟩
  have : PolishSpace Y := isClosed_closure.polishSpace
  have hY : ¬ IsMeagre (MulAction.orbit G xY) := by
    rw [← SubMulAction.val_preimage_orbit]
    exact hx
  have ho := isOpenMap_orbitMap_of_nonmeagre xY hY
  let e : MulAction.orbit G xY ≃ₜ MulAction.orbit G x :=
    { toEquiv :=
        { toFun := fun y => ⟨y.val.val, by
            obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.property
            exact MulAction.mem_orbit_iff.mpr ⟨g, congrArg Subtype.val hg⟩⟩
          invFun := fun y => ⟨⟨y.val, subset_closure y.property⟩, by
            rw [← SubMulAction.val_preimage_orbit]
            exact y.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact e.isOpenMap.comp ho

omit [IsTopologicalGroup G] in
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    and $\pi_x$ is a continuous bijection
    onto $G \cdot x$.
-/
/-- The canonical map from cosets of the stabilizer to the orbit is continuous. -/
theorem continuous_quotientStabilizerOrbitMap (x : X) :
    Continuous (MulAction.orbitEquivQuotientStabilizer G x).symm := by
  apply (QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x)).continuous_iff.mpr
  change Continuous (fun g : G =>
    (⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩ : MulAction.orbit G x))
  fun_prop

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    To prove openness, let $O\IncludedIn G$ be open and $h\in O$. Choose an open identity neighborhood $V$ with
    $hV\IncludedIn O$. The lemma shows that $hV\cdot x$ contains a relative neighborhood of $h\cdot x$ in the orbit.
    Thus every point of $O\cdot x$ is an interior point of that set, so $O\cdot x$ is open in the orbit.
    Applying this to the inverse image of an open subset of the quotient proves that
    $\pi_x:G/G_x\to G\cdot x$ is open. It is already a continuous bijection, hence a homeomorphism.
    \end{proof}
-/
/-- Nonmeagerness in the closure makes the canonical quotient-to-orbit
equivalence a homeomorphism. Its underlying function is unchanged. -/
noncomputable def quotientStabilizerOrbitHomeomorph
    [PolishSpace G] [PolishSpace X] (x : X)
    (hx : ¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x)))) :
    (G ⧸ MulAction.stabilizer G x) ≃ₜ MulAction.orbit G x :=
  (MulAction.orbitEquivQuotientStabilizer G x).symm.toHomeomorphOfContinuousOpen
    (continuous_quotientStabilizerOrbitMap x) (by
      intro U hU
      have he :
          (MulAction.orbitEquivQuotientStabilizer G x).symm '' U =
            (fun g : G =>
              (⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩ : MulAction.orbit G x)) ''
              (QuotientGroup.mk ⁻¹' U) := by
        change _ =
          ((MulAction.orbitEquivQuotientStabilizer G x).symm ∘ QuotientGroup.mk) ''
            (QuotientGroup.mk ⁻¹' U)
        rw [Set.image_comp,
          Set.image_preimage_eq _ (QuotientGroup.isQuotientMap_mk _).surjective]
      rw [he]
      exact isOpenMap_orbitMap_of_nonmeagre_in_closure x hx _
        (hU.preimage QuotientGroup.continuous_mk))

@[simp]
theorem quotientStabilizerOrbitHomeomorph_apply
    [PolishSpace G] [PolishSpace X] (x : X)
    (hx : ¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x))))
    (g : G) :
    (quotientStabilizerOrbitHomeomorph x hx (QuotientGroup.mk g) : X) = g • x :=
  rfl

end PolishSpaceBook
