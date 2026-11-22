module

public import PolishSpaceBook.CategoryLocalization
public import PolishSpaceBook.BorelCategoryQuantifiers
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

/-! # The operation and localization rules for Vaught transforms

The book uses star for the nonmeager transform and triangle for the
comeager transform. Borel-rank preservation is a separate induction.
-/
namespace PolishSpaceBook
open Set Topology TopologicalSpace

variable {G X : Type*} [Group G] [MulAction G X]

def actionRelation (A : Set X) : Set (G × X) := {p | p.1 • p.2 ∈ A}

@[simp] theorem actionRelation_compl (A : Set X) :
    actionRelation (G := G) Aᶜ = (actionRelation A)ᶜ := rfl

@[simp] theorem actionRelation_iUnion (A : ℕ → Set X) :
    actionRelation (G := G) (⋃ n, A n) = ⋃ n, actionRelation (A n) := by
  ext p; simp [actionRelation]

@[simp] theorem actionRelation_iInter (A : ℕ → Set X) :
    actionRelation (G := G) (⋂ n, A n) = ⋂ n, actionRelation (A n) := by
  ext p; simp [actionRelation]

variable [TopologicalSpace G]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    Fix a continuous action of a Polish group $G$ on a Polish space $X$, a set $A \IncludedIn X$, and a nonempty open $U
    \IncludedIn G$. Define
    $$\begin{aligned}
    A^{*U} &:= \{x \in X : \{g \in U : g \cdot x \in A\} \text{ is non-meager in } U\}, \\
    A^{\triangle U} &:= \{x \in X : \{g \in U : g \cdot x \in A\} \text{ is comeager in } U\}.
    \end{aligned}$$
    The two transforms are dual:
    $$\complement(A^{*U}) = (\complement A)^{\triangle U},$$
    since a subset of $U$ is meager if and only if its complement in $U$ is a \termuse{comeager set}.
    When $U = G$ we write simply $A^*$ and $A^{\triangle}$.
-/
def vaughtStar (U : Set G) (A : Set X) : Set X := categoryStar U (actionRelation A)

def vaughtTriangle (U : Set G) (A : Set X) : Set X := categoryTriangle U (actionRelation A)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The duality
    $$\complement(A^{*U})=(\complement A)^{\triangle U}$$
    is immediate from the definitions: a subset of the Baire space $U$ is non-meager iff its complement is not comeager.
-/
theorem vaughtStar_compl (U : Set G) (A : Set X) :
    (vaughtStar U A)ᶜ = vaughtTriangle U Aᶜ := by
  simp only [vaughtStar, vaughtTriangle, actionRelation_compl, categoryStar_compl]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem vaughtStar_iUnion (U : Set G) (A : ℕ → Set X) :
    vaughtStar U (⋃ n, A n) = ⋃ n, vaughtStar U (A n) := by
  simp only [vaughtStar, actionRelation_iUnion, categoryStar_iUnion]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem vaughtTriangle_iInter (U : Set G) (A : ℕ → Set X) :
    vaughtTriangle U (⋂ n, A n) = ⋂ n, vaughtTriangle U (A n) := by
  simp only [vaughtTriangle, actionRelation_iInter, categoryTriangle_iInter]

/-- Meagerness is invariant under a homeomorphism, in both directions. -/
theorem isMeagre_preimage_homeomorph_iff {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (S : Set Z) : IsMeagre (e ⁻¹' S) ↔ IsMeagre S := by
  constructor
  · intro h
    have hm := e.isEmbedding.isInducing.isMeagre_image h
    simpa only [image_preimage_eq _ e.surjective] using hm
  · exact fun h => h.preimage_of_isOpenMap e.continuous e.isOpenMap

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For (2), let $h \in G$ and $x \in A^*$. The set $\{g : g \cdot (h \cdot x) \in A\} = \{g : (gh) \cdot x \in A\}$ is the
    right-translate by $h^{-1}$ of $\{g : g \cdot x \in A\}$, hence still non-meager in $G$, since translation is a
    homeomorphism. This proves invariance of $A^*$. Applying the same result to the complement and using duality proves
    invariance of $A^{\triangle}$.
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem smul_mem_vaughtStar_univ_iff [IsTopologicalGroup G] (h : G) (x : X) (A : Set X) :
    h • x ∈ vaughtStar (univ : Set G) A ↔ x ∈ vaughtStar (univ : Set G) A := by
  change ¬ IsMeagre (relationSection (actionRelation A) (h • x) ∩ univ) ↔
    ¬ IsMeagre (relationSection (actionRelation A) x ∩ univ)
  simp only [inter_univ]
  have he : relationSection (actionRelation A) (h • x) =
      (Homeomorph.mulRight h) ⁻¹' relationSection (actionRelation A) x := by
    ext g; simp [relationSection, actionRelation, mul_smul]
  rw [he, isMeagre_preimage_homeomorph_iff]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem smul_mem_vaughtTriangle_univ_iff [IsTopologicalGroup G] (h : G) (x : X) (A : Set X) :
    h • x ∈ vaughtTriangle (univ : Set G) A ↔ x ∈ vaughtTriangle (univ : Set G) A := by
  have he : vaughtTriangle (univ : Set G) A = (vaughtStar (univ : Set G) Aᶜ)ᶜ := by
    simpa only [compl_compl] using (vaughtStar_compl (univ : Set G) Aᶜ).symm
  rw [he]
  exact not_congr (smul_mem_vaughtStar_univ_iff h x Aᶜ)

section Continuous
variable [TopologicalSpace X] [ContinuousSMul G X]

/-- Borel action sections have the Baire property needed by localization. -/
theorem baireMeasurable_actionSection [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : MeasurableSet A) (x : X) :
    BaireMeasurableSet (relationSection (actionRelation (G := G) A) x) := by
  borelize G
  have hc : Continuous (fun g : G => g • x) := by fun_prop
  exact (hA.preimage hc.measurable).baireMeasurableSet

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem vaughtTriangle_iUnion [BaireSpace G] [MeasurableSpace X] [BorelSpace X]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) :
    vaughtTriangle U (⋃ n, A n) =
      ⋂ V ∈ B, ⋂ (_ : V.Nonempty), ⋂ (_ : V ⊆ U), ⋃ n, vaughtStar V (A n) := by
  simpa only [vaughtTriangle, vaughtStar, actionRelation_iUnion] using
    categoryTriangle_iUnion hB hU (fun n => actionRelation (A n))
      (fun n x => baireMeasurable_actionSection (hA n) x)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem vaughtStar_iInter [BaireSpace G] [MeasurableSpace X] [BorelSpace X]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) :
    vaughtStar U (⋂ n, A n) =
      ⋃ V ∈ B, ⋃ (_ : V.Nonempty), ⋃ (_ : V ⊆ U), ⋂ n, vaughtTriangle V (A n) := by
  simpa only [vaughtTriangle, vaughtStar, actionRelation_iInter] using
    categoryStar_iInter hB hU (fun n => actionRelation (A n))
      (fun n x => baireMeasurable_actionSection (hA n) x)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    It remains to justify Borelness. Let $A$ be open. The set
    $$
    R_A:=\{(x,g)\in X\times U:g\cdot x\in A\}
    $$
    is open. For fixed $x$, the section $(R_A)_x$ is open in $U$, and an open subset of a Baire space is non-meager iff it
    is nonempty. Thus
    $$
    A^{*U}=\{x:\exists g\in U,\ g\cdot x\in A\}.
    $$
    The right-hand side is open: for each fixed $g\in U$, the set $\{x:g\cdot x\in A\}$ is open by continuity, and
    $A^{*U}$ is their union. Moreover, the section of an open $A$ is open in $U$, so it is comeager exactly when it is
    dense. Therefore
    $$
    A^{\triangle U}
    =\bigcap_{\substack{W\in\mathcal U\\\emptyset\ne W\IncludedIn U}}A^{*W},
    $$
    which is $\bPi^0_2$.
-/
theorem vaughtStar_open_eq [BaireSpace G] {U : Set G} (hU : IsOpen U)
    {A : Set X} (hA : IsOpen A) :
    vaughtStar U A = {x | ∃ g ∈ U, g • x ∈ A} :=
  categoryStar_open_eq hU (hA.preimage continuous_smul)

theorem isOpen_vaughtStar [BaireSpace G] {U : Set G} (hU : IsOpen U)
    {A : Set X} (hA : IsOpen A) : IsOpen (vaughtStar U A) :=
  isOpen_categoryStar hU (hA.preimage continuous_smul)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For (3), if $A$ is open and $x \in A$, then $\{g : g \cdot x \in A\}$ contains the open neighborhood of $e$ obtained by
    continuity of the action at $(e, x)$, hence is non-meager.
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem subset_vaughtStar_univ_of_isOpen [BaireSpace G] {A : Set X} (hA : IsOpen A) :
    A ⊆ vaughtStar (univ : Set G) A := by
  rw [vaughtStar_open_eq isOpen_univ hA]
  intro x hx
  exact ⟨1, mem_univ _, by simpa using hx⟩

theorem isGdelta_vaughtTriangle_of_isOpen [BaireSpace G]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) (hBc : B.Countable)
    {U : Set G} (hU : IsOpen U) {A : Set X} (hA : IsOpen A) :
    IsGδ (vaughtTriangle U A) :=
  isGdelta_categoryTriangle_open hB hBc hU (hA.preimage continuous_smul)

/-- Borelness of both transforms is the general section-quantifier theorem applied to the action. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The \termdefineas{Vaught transform}{Vaught transforms} [@Vaught1974] are the main tool for translating
    Baire-category statements about $G$ into Borel statements about $X$. They convert a Borel set $A \IncludedIn
    X$ into a Borel
    set
    encoding "many group elements move a point into $A$."
-/
theorem measurable_vaught_transforms [PolishSpace G] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {A : Set X} (hA : MeasurableSet A)
    (U : Set G) (hU : IsOpen U) :
    MeasurableSet (vaughtStar U A) ∧ MeasurableSet (vaughtTriangle U A) := by
  borelize G
  exact measurable_category_quantifiers_polish
    (hA.preimage continuous_smul.measurable) U hU

end Continuous
end PolishSpaceBook
