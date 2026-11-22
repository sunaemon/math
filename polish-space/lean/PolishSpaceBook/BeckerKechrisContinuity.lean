module

public import PolishSpaceBook.VaughtTransforms

@[expose] public section

/-! # Continuity in the Vaught-transform topology

The Polish basis construction is cited external infrastructure in the book.
Here its transform topology is used explicitly: the action preimage of a
subbasic set is a union of product-open rectangles. No continuity of the
original Borel action is assumed.
-/

namespace PolishSpaceBook.BeckerKechris

open Set Topology TopologicalSpace Filter
open scoped Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] We use a right-handed notation for the Vaught transform. For an open $U\IncludedIn G$ and a Borel
    $A\IncludedIn X$, put
    $$
    U\star A:=\{x\in X:\{u\in U:u^{-1}\cdot x\in A\}\text{ is non-meager in }U\}.
    $$
    Thus $U\star A=A^{*U^{-1}}$ in the notation of §{sec:vaught-transforms}. The Borel-action form of Vaught's lemma says
    that $U\star A$ is Borel whenever $A$ is Borel. Indeed,
    $$
    R_A:=\{(u,x):u^{-1}\cdot x\in A\}
    $$
    is Borel, and the non-meager category quantifier applied to $R_A\cap(U\times X)$ is Borel by the preceding lemma.
-/
/-- The inverse-action relation used for the right-handed transform. -/
def inverseActionRelation (A : Set X) : Set (G × X) := {p | p.1⁻¹ • p.2 ∈ A}

/-- Nonmeagerness of the inverse-action section in an open group set. -/
def rightVaughtStar (U : Set G) (A : Set X) : Set X :=
  categoryStar U (inverseActionRelation A)

omit [IsTopologicalGroup G] in
/-- On an open group set, the ambient definition is exactly nonmeagerness
in the relative topology used in the book. -/
theorem mem_rightVaughtStar_iff {U : Set G} (hU : IsOpen U) (A : Set X) (x : X) :
    x ∈ rightVaughtStar U A ↔ ¬ IsMeagre {u : U | (u : G)⁻¹ • x ∈ A} :=
  mem_categoryStar_iff hU (inverseActionRelation A) x

/-- Inverting the group variable identifies the two conventions for Vaught transforms. -/
theorem rightVaughtStar_eq (U : Set G) (A : Set X) :
    rightVaughtStar U A = vaughtStar (Inv.inv ⁻¹' U) A := by
  ext x
  change ¬ IsMeagre (relationSection (inverseActionRelation (G := G) A) x ∩ U) ↔
    ¬ IsMeagre (relationSection (actionRelation A) x ∩ (Inv.inv ⁻¹' U))
  have he : (Homeomorph.inv G) ⁻¹' (relationSection (inverseActionRelation (G := G) A) x ∩ U) =
      relationSection (actionRelation A) x ∩ (Inv.inv ⁻¹' U) := by
    ext g
    simp [relationSection, inverseActionRelation, actionRelation]
  rw [← he, isMeagre_preimage_homeomorph_iff]

/-- Left translation transfers nonmeagerness to the translated open set. -/
theorem smul_mem_rightVaughtStar_iff (g : G) (x : X) (U : Set G) (A : Set X) :
    g • x ∈ rightVaughtStar U A ↔
      x ∈ rightVaughtStar ((fun w => g * w) ⁻¹' U) A := by
  change ¬ IsMeagre (relationSection (inverseActionRelation (G := G) A) (g • x) ∩ U) ↔
    ¬ IsMeagre (relationSection (inverseActionRelation (G := G) A) x ∩ ((fun w => g * w) ⁻¹' U))
  have he : (Homeomorph.mulLeft g) ⁻¹'
        (relationSection (inverseActionRelation (G := G) A) (g • x) ∩ U) =
      relationSection (inverseActionRelation (G := G) A) x ∩ ((fun w => g * w) ⁻¹' U) := by
    ext w
    simp [relationSection, inverseActionRelation, mul_smul]
  rw [← he, isMeagre_preimage_homeomorph_iff]

omit [IsTopologicalGroup G] in
/-- Enlarging the open group set preserves nonmeagerness. -/
theorem rightVaughtStar_mono {U V : Set G} (hUV : U ⊆ V) (A : Set X) :
    rightVaughtStar U A ⊆ rightVaughtStar V A := by
  intro x hx hm
  exact hx (hm.mono (inter_subset_inter_right _ hUV))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Choose a countable basis $\mathcal U$ for $G$, closed under finite intersections. We will use the following immediate
    product-refinement fact: if $O$ is nonempty open and $gO\IncludedIn U$ with $U$ open, then there are
    $V,W_0\in\mathcal U$ such that
    $g\in V$, $\emptyset\ne W_0\IncludedIn O$, and $VW_0\IncludedIn U$.
    Choose $w\in O$. Continuity of multiplication gives open neighborhoods $V'$ of $g$ and $W'$ of $w$
    with $V'W'\IncludedIn U$. Choose basic neighborhoods $V\IncludedIn V'$ of $g$ and
    $W_0\IncludedIn W'\cap O$ of $w$. These have the required properties.
-/
/-- Continuity of multiplication supplies small basic rectangles at a chosen
point of the nonempty open set. -/
theorem exists_basis_product {B : Set (Set G)} (hB : IsTopologicalBasis B)
    (g : G) {O U : Set G} (hO : IsOpen O) (hn : O.Nonempty) (hU : IsOpen U)
    (hOU : ∀ w ∈ O, g * w ∈ U) :
    ∃ V ∈ B, ∃ W ∈ B, g ∈ V ∧ W.Nonempty ∧ W ⊆ O ∧ V * W ⊆ U := by
  obtain ⟨w, hw⟩ := hn
  have hp : (fun p : G × G => p.1 * p.2) ⁻¹' U ∈ 𝓝 (g, w) :=
    (hU.preimage continuous_mul).mem_nhds (hOU w hw)
  obtain ⟨V', hV', W', hW', hVW⟩ := mem_nhds_prod_iff.mp hp
  obtain ⟨V, hVB, hgV, hVV⟩ := hB.mem_nhds_iff.mp hV'
  obtain ⟨W, hWB, hwW, hWW⟩ := hB.mem_nhds_iff.mp (inter_mem hW' (hO.mem_nhds hw))
  refine ⟨V, hVB, W, hWB, hgV, ⟨w, hwW⟩, fun x hx => (hWW hx).2, ?_⟩
  rintro _ ⟨v, hv, w, hw, rfl⟩
  exact hVW (a := (v, w)) ⟨hVV hv, (hWW hw).1⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    First suppose $g\in V$, $x\in W\star A$, and $VW\IncludedIn U$. For non-meagerly many $w\in W$ we have
    $w^{-1}\cdot x\in A$. For those $w$, put $u=gw\in U$. Then
    $$
    u^{-1}\cdot(g\cdot x)=w^{-1}\cdot x\in A,
    $$
    and the image of a non-meager subset of $W$ under the homeomorphism $w\mapsto gw$ is non-meager in $gW\IncludedIn U$,
    hence non-meager in $U$. Thus $g\cdot x\in U\star A$.
-/
/-- Every rectangle on the proposed right-hand side maps into the transform. -/
theorem smul_mem_of_product_subset {V W U : Set G} (hVW : V * W ⊆ U)
    {g : G} (hg : g ∈ V) {x : X} {A : Set X} (hx : x ∈ rightVaughtStar W A) :
    g • x ∈ rightVaughtStar U A := by
  rw [smul_mem_rightVaughtStar_iff]
  apply rightVaughtStar_mono (V := (fun w : G => g * w) ⁻¹' U) ?_ A hx
  intro w hw
  exact hVW (Set.mul_mem_mul hg hw)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Conversely, suppose $g\cdot x\in U\star A$. Then
    $$
    M:=\{u\in U:u^{-1}\cdot(g\cdot x)\in A\}
    $$
    is non-meager in $U$. Write
    $$C_x:=\{w\in G:w^{-1}\cdot x\in A\}.$$
    The identity $(gw)^{-1}\cdot(g\cdot x)=w^{-1}\cdot x$ gives
    $$g^{-1}M=C_x\cap g^{-1}U.$$
    Left translation is a homeomorphism, so this intersection is non-meager in the open set $g^{-1}U$.
    The set $C_x$ is Borel, since the action is Borel. Baire-property localization therefore gives a nonempty open
    $O\IncludedIn g^{-1}U$ on which $C_x$ is comeager. Now $gO\IncludedIn U$, so product refinement gives
    $V,W_0\in\mathcal U$ with $g\in V$, $\emptyset\ne W_0\IncludedIn O$, and $VW_0\IncludedIn U$.
    The set $C_x\cap W_0$ is comeager, hence non-meager, in $W_0$. Thus $x\in W_0\star A$, so $(g,x)$ belongs to the
    right-hand side.
-/
/-- Localizing a Baire section to a comeager open piece produces a basic
rectangle around any pair whose product lies in the transform. -/
theorem exists_rectangle_of_smul_mem [BaireSpace G]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    {A : Set X} {g : G} {x : X}
    (hA : BaireMeasurableSet (relationSection (inverseActionRelation (G := G) A) x))
    (hx : g • x ∈ rightVaughtStar U A) :
    ∃ V ∈ B, ∃ W ∈ B, V * W ⊆ U ∧ g ∈ V ∧ x ∈ rightVaughtStar W A := by
  rw [smul_mem_rightVaughtStar_iff] at hx
  obtain ⟨O, hO, hn, hOU, hOA⟩ := baire_localization_ambient hA
    (hU.preimage (continuous_const.mul continuous_id)) hx
  obtain ⟨V, hVB, W, hWB, hgV, hnW, hWO, hVW⟩ :=
    exists_basis_product hB g hO hn hU (fun w hw => hOU hw)
  refine ⟨V, hVB, W, hWB, hVW, hgV, ?_⟩
  change ¬ IsMeagre (relationSection (inverseActionRelation (G := G) A) x ∩ W)
  have hm : IsMeagre (W \ relationSection (inverseActionRelation (G := G) A) x) := by
    apply IsMeagre.mono ?_ hOA
    intro w hw
    exact ⟨hWO hw.1, hw.2⟩
  exact not_isMeagre_inter_of_comeagre (hB.isOpen hWB) hnW subset_rfl hm

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    It remains to prove that the action is continuous for this topology. It is enough to check the subbasic sets
    $U\star A\in\mathcal S$. We claim that
    $$
    \alpha^{-1}(U\star A)
    =\bigcup\{\,V\times(W\star A):V,W\in\mathcal U,\ VW\IncludedIn U\,\}.
    $$
-/
/-- The action preimage is the union of basic product rectangles. -/
theorem preimage_rightVaughtStar [BaireSpace G]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    {A : Set X} (hA : ∀ x, BaireMeasurableSet (relationSection (inverseActionRelation (G := G) A) x)) :
    (fun p : G × X => p.1 • p.2) ⁻¹' rightVaughtStar U A =
      ⋃ V ∈ B, ⋃ W ∈ B, ⋃ (_ : V * W ⊆ U), V ×ˢ rightVaughtStar W A := by
  ext p
  simp only [mem_preimage, mem_iUnion, mem_prod, exists_prop]
  constructor
  · exact exists_rectangle_of_smul_mem hB hU (hA p.2)
  · rintro ⟨V, _, W, _, hVW, hgV, hx⟩
    exact smul_mem_of_product_subset hVW hgV hx

/-- The new topology uses only transform sets as its subbasis. -/
@[implicit_reducible]
def transformTopology (B : Set (Set G)) (C : Set (Set X)) : TopologicalSpace X :=
  .generateFrom (Set.image2 rightVaughtStar B C)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    The displayed identity writes the preimage of each subbasic open set as a union of product-open sets in
    $G\times(X,\tau)$, because every $W\star A$ is itself subbasic. Therefore
    $\alpha:G\times(X,\tau)\to(X,\tau)$ is continuous. The constructed $\tau$ is Polish and has exactly the original Borel
    $\sigma$-algebra, as required.
-/
/-- The rectangle identity proves continuity for the generated topology,
without assuming that the action was continuous in an earlier topology. -/
theorem continuousSMul_transformTopology [BaireSpace G]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) (C : Set (Set X))
    (hC : ∀ A ∈ C, ∀ x, BaireMeasurableSet (relationSection (inverseActionRelation (G := G) A) x)) :
    letI := transformTopology B C
    ContinuousSMul G X := by
  let := transformTopology B C
  constructor
  apply continuous_generateFrom_iff.mpr
  rintro S ⟨U, hUB, A, hAC, rfl⟩
  rw [preimage_rightVaughtStar hB (hB.isOpen hUB) (hC A hAC)]
  apply isOpen_iUnion
  intro V
  apply isOpen_iUnion
  intro hVB
  apply isOpen_iUnion
  intro W
  apply isOpen_iUnion
  intro hWB
  apply isOpen_iUnion
  intro _
  exact (hB.isOpen hVB).prod (TopologicalSpace.isOpen_generateFrom_of_mem ⟨W, hWB, A, hAC, rfl⟩)

section Borel

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X]

/-- Inversion and the Borel action give a Borel inverse-action relation. -/
theorem measurable_inverseActionRelation
    (hact : Measurable (fun p : G × X => p.1 • p.2))
    {A : Set X} (hA : MeasurableSet A) : MeasurableSet (inverseActionRelation (G := G) A) :=
  hA.preimage (hact.comp ((continuous_inv.measurable.comp measurable_fst).prodMk measurable_snd))

/-- Each inverse-action section is Borel and hence has the Baire property. -/
theorem baireMeasurable_inverseActionSection
    (hact : Measurable (fun p : G × X => p.1 • p.2))
    {A : Set X} (hA : MeasurableSet A) (x : X) :
    BaireMeasurableSet (relationSection (inverseActionRelation (G := G) A) x) :=
  ((measurable_inverseActionRelation hact hA).preimage
    (measurable_id.prodMk measurable_const)).baireMeasurableSet

/-- Borel category quantification proves Borelness of the right-handed transform. -/
theorem measurable_rightVaughtStar [PolishSpace G] [StandardBorelSpace X]
    (hact : Measurable (fun p : G × X => p.1 • p.2))
    {A : Set X} (hA : MeasurableSet A) {U : Set G} (hU : IsOpen U) :
    MeasurableSet (rightVaughtStar U A) :=
  (measurable_category_quantifiers (measurable_inverseActionRelation hact hA) U hU).1

/-- For a Borel action, every family of Borel sets satisfies the section
hypothesis of the continuity theorem. -/
theorem continuousSMul_transformTopology_of_measurable [BaireSpace G]
    (hact : Measurable (fun p : G × X => p.1 • p.2))
    {B : Set (Set G)} (hB : IsTopologicalBasis B) (C : Set (Set X))
    (hC : ∀ A ∈ C, MeasurableSet A) :
    letI := transformTopology B C
    ContinuousSMul G X :=
  continuousSMul_transformTopology hB C
    (fun A hAC x => baireMeasurable_inverseActionSection hact (hC A hAC) x)

/-- The cited Polish basis construction supplies the family and its topology;
the local rectangle proof supplies the missing continuity conclusion. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    Every Borel action admits a compatible Polish topology that makes the action continuous. We use the Polish
    basis construction from the proof of [@BeckerKechris1996, Theorem 5.2.1] as an external input, and verify the
    continuity step below. The old topology on the space is not retained as an open subbasis; the new subbasis consists
    of Vaught transforms.
-/
theorem beckerKechris_of_polish_basis_construction [PolishSpace G]
    (hact : Measurable (fun p : G × X => p.1 • p.2))
    (hconstruction : ∃ (B : Set (Set G)) (C : Set (Set X)),
      IsTopologicalBasis B ∧ B.Countable ∧ C.Countable ∧
      (∀ A ∈ C, MeasurableSet A) ∧
      (letI := transformTopology B C; PolishSpace X ∧ BorelSpace X)) :
    ∃ t : TopologicalSpace X, letI := t
      PolishSpace X ∧ BorelSpace X ∧ ContinuousSMul G X := by
  obtain ⟨B, C, hB, _, _, hC, hP, hBor⟩ := hconstruction
  refine ⟨transformTopology B C, hP, hBor, ?_⟩
  exact continuousSMul_transformTopology_of_measurable hact hB C hC

end Borel
end PolishSpaceBook.BeckerKechris
