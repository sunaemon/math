module

public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.OpenSubgroup
public import PolishSpaceBook.PolishSpaces

@[expose] public section

/-! # Local Baire category and the book's Pettis argument

The proofs work in a Baire topological group. Polishness supplies this
hypothesis in the chapter. Relative meagerness in an open set is related
explicitly to ambient meagerness before using translation homeomorphisms.
-/

namespace PolishSpaceBook
open Set Topology Filter
open scoped Pointwise

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    For a subset of an open subspace, being meager in that subspace is equivalent to being meager in the ambient space.
    Indeed, nowhere dense sets remain nowhere dense when included from a subspace, and intersecting a nowhere dense set
    with an open subspace preserves relative nowhere density. Passing to countable unions gives the equivalence.
    We use this to pass between relative and ambient category in the following proofs.
-/
/-- Relative and ambient meagerness agree inside an open subspace. -/
theorem isMeagre_in_open_iff {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    IsMeagre (Subtype.val ⁻¹' A : Set U) ↔ IsMeagre (A ∩ U) := by
  constructor
  · intro h
    have he : Subtype.val '' (Subtype.val ⁻¹' A : Set U) = A ∩ U := by
      ext x
      simp only [mem_image, mem_preimage, mem_inter_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
      · rintro ⟨ha, hu⟩; exact ⟨⟨x, hu⟩, ha, rfl⟩
    rw [← he]
    exact h.image_val
  · intro h
    have he : (Subtype.val ⁻¹' (A ∩ U) : Set U) = Subtype.val ⁻¹' A := by
      ext x
      simp
    rw [← he]
    exact h.preimage_of_isOpenMap continuous_subtype_val hU.isOpenMap_subtype_val

/-- Localization by the open representative of a Baire-measurable set. -/
theorem baire_localization_ambient {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hA : BaireMeasurableSet A) (hU : IsOpen U)
    (hne : ¬ IsMeagre (A ∩ U)) :
    ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧ IsMeagre (V \ A) := by
  obtain ⟨O, hO, hAO⟩ := hA.residualEq_isOpen
  have hAU : IsMeagre (A \ O) := by
    change ∀ᶠ x in residual X, x ∉ A \ O
    filter_upwards [hAO] with x hx h
    exact h.2 (hx.mp h.1)
  have hOA : IsMeagre (O \ A) := by
    change ∀ᶠ x in residual X, x ∉ O \ A
    filter_upwards [hAO] with x hx h
    exact h.2 (hx.mpr h.1)
  refine ⟨O ∩ U, hO.inter hU, ?_, inter_subset_right, hOA.mono ?_⟩
  · by_contra h
    apply hne
    apply hAU.mono
    rintro x ⟨hxA, hxU⟩
    exact ⟨hxA, fun hxO => h ⟨x, hxO, hxU⟩⟩
  · rintro x ⟨⟨hxO, _⟩, hxA⟩
    exact ⟨hxO, hxA⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Choose an open $O$ such that $A\mathbin{\triangle} O$ is meager. The set $O\cap U$ must be nonempty, since otherwise
    $A\cap U$ would be meager. Take $V=O\cap U$. The set $\SetDifference{V}{A}$ is contained in
    $A\mathbin{\triangle} O$, so it is meager in the ambient space and also in the open subspace $V$.
    Thus $A\cap V$ is comeager in $V$.
    \end{proof}
-/
/-- The statement in the book uses category in the relative open subspaces. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: lemma
  title: Baire-property localization
-/
theorem baire_localization {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hA : BaireMeasurableSet A) (hU : IsOpen U)
    (hne : ¬ IsMeagre (Subtype.val ⁻¹' A : Set U)) :
    ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      (Subtype.val ⁻¹' A : Set V) ∈ residual V := by
  obtain ⟨V, hV, hn, hVU, hVA⟩ :=
    baire_localization_ambient hA hU (fun h => hne ((isMeagre_in_open_iff hU).mpr h))
  refine ⟨V, hV, hn, hVU, ?_⟩
  have hm : IsMeagre (Subtype.val ⁻¹' Aᶜ : Set V) := by
    apply (isMeagre_in_open_iff hV).mpr
    simpa only [sdiff_eq, inter_comm] using hVA
  simpa only [IsMeagre, ← preimage_compl, compl_compl] using hm

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    By \termuse{Baire-property localization}, choose a nonempty open $U$ in which $A$ is comeager, and choose $g\in U$.
    Set
    $$W:=\{h\in G:gh\in U\}.$$
    Left translation is a homeomorphism, so $W$ is open and contains the identity. For $h\in W$, put
    $$H:=U\cap Uh^{-1},\qquad
    N:=\SetDifference{U}{A}\;\cup\;(\SetDifference{U}{A})h^{-1}.$$
    The open set $H$ is nonempty because it contains $g$. The set $\SetDifference{U}{A}$ is meager in $G$ by the
    open-subspace observation above. Right translation preserves meagerness, so $N$ is meager.
    Since a nonempty open subset of the Baire space $G$ cannot be meager, choose $a\in\SetDifference{H}{N}$.
    Then $a\in A$ and $ah\in A$, hence
    $$h=a^{-1}(ah)\in A^{-1}A.$$
    Thus $W\IncludedIn A^{-1}A$.
    \end{proof}
-/
/-- Choose two points of `A` in a common translated open set, as in the book. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: lemma
  title: Pettis
-/
theorem pettis_open_identity_neighborhood {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
    {A : Set G} (hA : BaireMeasurableSet A) (hne : ¬ IsMeagre A) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ W ⊆ A⁻¹ * A := by
  obtain ⟨U, hU, ⟨g, hg⟩, _, hUA⟩ :=
    baire_localization_ambient hA isOpen_univ (by simpa using hne)
  let W := (fun h : G => g * h) ⁻¹' U
  refine ⟨W, hU.preimage (Homeomorph.mulLeft g).continuous, by simpa [W] using hg, ?_⟩
  intro h hh
  let S := U ∩ (fun a : G => a * h) ⁻¹' U
  have hS : IsOpen S := hU.inter (hU.preimage (Homeomorph.mulRight h).continuous)
  have hSn : S.Nonempty := ⟨g, hg, hh⟩
  let N := (U \ A) ∪ (fun a : G => a * h) ⁻¹' (U \ A)
  have hN : IsMeagre N := hUA.union
    (hUA.preimage_of_isOpenMap (Homeomorph.mulRight h).continuous (isOpenMap_mul_right h))
  have hex : ∃ a ∈ S, a ∉ N := by
    by_contra! hsub
    exact not_isMeagre_of_isOpen hS hSn (hN.mono hsub)
  obtain ⟨a, haS, haN⟩ := hex
  have ha : a ∈ A := by
    by_contra hn
    exact haN (Or.inl ⟨haS.1, hn⟩)
  have hah : a * h ∈ A := by
    by_contra hn
    exact haN (Or.inr ⟨haS.2, hn⟩)
  exact mem_mul.mpr ⟨a⁻¹, by simpa using ha, a * h, hah, by simp⟩

/-- A nonmeager Baire-measurable subgroup is open by Pettis. -/
theorem isOpen_baire_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [BaireSpace G] (H : Subgroup G)
    (hH : BaireMeasurableSet (H : Set G)) (hne : ¬ IsMeagre (H : Set G)) :
    IsOpen (H : Set G) := by
  obtain ⟨W, hW, h1, hWH⟩ := pettis_open_identity_neighborhood hH hne
  apply H.isOpen_of_mem_nhds (g := 1)
  apply mem_of_superset (hW.mem_nhds h1)
  intro h hh
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp (hWH hh)
  exact H.mul_mem (by simpa using ha) hb

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $K=\Closure{H}$, a closed subgroup of $G$ and hence a Polish group. By Alexandrov's theorem in
    §{sec:alexandrov-theorem}, $H$ is a dense $\Gdelta$ subset of $K$, so it has the Baire property and is non-meager in
    $K$.
    Pettis's theorem gives an identity neighborhood in $K$ contained in $H^{-1}H=H$.
    Translating this neighborhood by elements of $H$ shows that $H$ is open in $K$. Its other cosets are open as well,
    so $H$ is also closed in $K$. As it is dense there, $H=K$, which proves that $H$ is closed in $G$.
    \end{proof}
-/
/-- A Polish subgroup is closed: work in its closure, then use Pettis. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: corollary
  title: Polish subgroups are closed
-/
theorem isClosed_polish_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] (H : Subgroup G) [PolishSpace H] :
    IsClosed (H : Set G) := by
  let K := H.topologicalClosure
  let R : Subgroup K := H.subgroupOf K
  have hK : IsClosed (K : Set G) := H.isClosed_topologicalClosure
  let : PolishSpace K := hK.polishSpace
  borelize (↥K)
  have hG : IsGδ (R : Set K) :=
    IsGδ.preimage (f := (Subtype.val : K → G)) continuous_subtype_val
      (polish_subspace_isGdelta (A := (H : Set G)))
  have himage : (Subtype.val : K → G) '' (R : Set K) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx
      exact ⟨⟨x, H.le_topologicalClosure hx⟩, hx, rfl⟩
  have hd : Dense (R : Set K) := by
    apply Subtype.dense_iff.mpr
    change (K : Set G) ⊆ closure ((Subtype.val : K → G) '' (R : Set K))
    rw [himage]
    exact subset_rfl
  have ho : IsOpen (R : Set K) :=
    isOpen_baire_subgroup R hG.measurableSet.baireMeasurableSet
      (not_isMeagre_of_isGδ_of_dense hG hd)
  have hc : IsClosed (R : Set K) := R.isClosed_of_isOpen ho
  have htop : (R : Set K) = univ := hc.closure_eq.symm.trans hd.closure_eq
  apply isClosed_of_closure_subset
  intro x hx
  have hr : (⟨x, hx⟩ : K) ∈ (R : Set K) := by rw [htop]; trivial
  exact hr

end PolishSpaceBook
