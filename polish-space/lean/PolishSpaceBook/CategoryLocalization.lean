module

public import PolishSpaceBook.PolishGroupCategory

@[expose] public section

/-! # Category localization on an open basis

These facts concern sections of arbitrary relations. The Vaught transforms
and the later Borel category quantifiers share the same localization proof.
-/
namespace PolishSpaceBook
open Set Topology TopologicalSpace Filter

variable {G : Type*} [TopologicalSpace G]

/-- A countable union is meager exactly when all its terms are meager. -/
theorem isMeagre_iUnion_iff_book (A : ℕ → Set G) :
    IsMeagre (⋃ n, A n) ↔ ∀ n, IsMeagre (A n) :=
  ⟨fun h n => h.mono (subset_iUnion A n), isMeagre_iUnion⟩

/-- A nonempty open set cannot be covered by two meager exceptional sets. -/
theorem not_isMeagre_inter_of_comeagre [BaireSpace G]
    {A V U : Set G} (hV : IsOpen V) (hn : V.Nonempty) (hVU : V ⊆ U)
    (hVA : IsMeagre (V \ A)) : ¬ IsMeagre (A ∩ U) := by
  intro hAU
  apply not_isMeagre_of_isOpen hV hn
  apply (hAU.union hVA).mono
  intro x hx
  by_cases h : x ∈ A
  · exact Or.inl ⟨h, hVU hx⟩
  · exact Or.inr ⟨hx, h⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    The localization rules depend only on the Baire property of the sections. Let $C\IncludedIn G$ have the Baire
    property. If $C\cap U$ is non-meager in $U$, Baire-property localization gives a nonempty open subset of $U$
    on which $C$ is comeager. Choose a nonempty basic open $W$ inside that subset; then $C\cap W$ is comeager in $W$.
    Conversely, if $C\cap W$ is comeager in a nonempty basic $W\IncludedIn U$ but $C\cap U$ is meager, both terms in
    $$W=(C\cap W)\cup(\SetDifference{W}{C})$$
    are meager, contradicting that the nonempty open subspace $W$ is a Baire space.

    Also, $C\cap U$ is comeager in $U$ if and only if $C\cap W$ is non-meager in every nonempty basic $W\IncludedIn U$.
    For the forward direction, the same decomposition of $W$ rules out meagerness of $C\cap W$.
    For the converse, if $\SetDifference{U}{C}$ were non-meager, apply the preceding localization result to the complement
    of $C$. It gives a nonempty basic $W\IncludedIn U$ on which $C\cap W$ is meager, a contradiction.

    Apply the second equivalence to the section of $\bigcup_nA_n$, then use the direct union rule inside each basic $W$.
    This gives the first localization formula. Apply the first equivalence to the section of $\bigcap_nA_n$ and use the
    direct intersection rule for comeagerness to obtain the second formula. Borel sections have the Baire property, so
    these arguments apply to the sets in the statement.
-/
/-- Nonmeagerness localizes to comeagerness in a nonempty basic open set. -/
theorem nonmeagre_iff_exists_basis_comeagre [BaireSpace G]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {A U : Set G}
    (hA : BaireMeasurableSet A) (hU : IsOpen U) :
    ¬ IsMeagre (A ∩ U) ↔
      ∃ V ∈ B, V.Nonempty ∧ V ⊆ U ∧ IsMeagre (V \ A) := by
  constructor
  · intro h
    obtain ⟨O, hO, ⟨x, hx⟩, hOU, hOA⟩ := baire_localization_ambient hA hU h
    obtain ⟨V, hVB, hxV, hVO⟩ := hB.exists_subset_of_mem_open hx hO
    exact ⟨V, hVB, ⟨x, hxV⟩, hVO.trans hOU,
      hOA.mono (show V \ A ⊆ O \ A from fun _ h => ⟨hVO h.1, h.2⟩)⟩
  · rintro ⟨V, hVB, hn, hVU, hVA⟩
    exact not_isMeagre_inter_of_comeagre (hB.isOpen hVB) hn hVU hVA

/-- Comeagerness means nonmeagerness in every nonempty basic open subset. -/
theorem comeagre_iff_forall_basis_nonmeagre [BaireSpace G]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {A U : Set G}
    (hA : BaireMeasurableSet A) (hU : IsOpen U) :
    IsMeagre (U \ A) ↔
      ∀ V ∈ B, V.Nonempty → V ⊆ U → ¬ IsMeagre (A ∩ V) := by
  constructor
  · intro h V hVB hn hVU
    exact not_isMeagre_inter_of_comeagre (hB.isOpen hVB) hn subset_rfl
      (h.mono (show V \ A ⊆ U \ A from fun _ hx => ⟨hVU hx.1, hx.2⟩))
  · intro h
    by_contra hn
    have hn' : ¬ IsMeagre (Aᶜ ∩ U) := by simpa only [sdiff_eq, inter_comm] using hn
    obtain ⟨V, hVB, hVn, hVU, hVA⟩ :=
      (nonmeagre_iff_exists_basis_comeagre hB hA.compl hU).mp hn'
    apply h V hVB hVn hVU
    simpa only [sdiff_eq, compl_compl, inter_comm] using hVA

/-- A section is the inverse image under insertion of the parameter. -/
def relationSection {X : Type*} (R : Set (G × X)) (x : X) : Set G :=
  (fun g => (g, x)) ⁻¹' R

def categoryStar {X : Type*} (U : Set G) (R : Set (G × X)) : Set X :=
  {x | ¬ IsMeagre (relationSection R x ∩ U)}

def categoryTriangle {X : Type*} (U : Set G) (R : Set (G × X)) : Set X :=
  {x | IsMeagre (U \ relationSection R x)}

/-- The ambient definition agrees with the relative nonmeager quantifier. -/
theorem mem_categoryStar_iff {X : Type*} {U : Set G} (hU : IsOpen U)
    (R : Set (G × X)) (x : X) :
    x ∈ categoryStar U R ↔ ¬ IsMeagre (Subtype.val ⁻¹' relationSection R x : Set U) :=
  not_congr (isMeagre_in_open_iff hU).symm

/-- The ambient definition agrees with the relative residual quantifier. -/
theorem mem_categoryTriangle_iff {X : Type*} {U : Set G} (hU : IsOpen U)
    (R : Set (G × X)) (x : X) :
    x ∈ categoryTriangle U R ↔ (Subtype.val ⁻¹' relationSection R x : Set U) ∈ residual U := by
  change IsMeagre (U \ relationSection R x) ↔ _
  rw [sdiff_eq, inter_comm, ← isMeagre_in_open_iff hU]
  simp only [IsMeagre, ← preimage_compl, compl_compl]

theorem categoryStar_compl {X : Type*} (U : Set G) (R : Set (G × X)) :
    (categoryStar U R)ᶜ = categoryTriangle U Rᶜ := by
  ext x
  simp [categoryStar, categoryTriangle, relationSection, inter_comm]

theorem categoryTriangle_compl {X : Type*} (U : Set G) (R : Set (G × X)) :
    (categoryTriangle U R)ᶜ = categoryStar U Rᶜ := by
  have h := congrArg compl (categoryStar_compl U Rᶜ)
  simpa only [compl_compl] using h.symm

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For countable unions,
    $$
    x\in\Big(\bigcup_n A_n\Big)^{*U}
    $$
    means that
    $$
    \{g\in U:g\cdot x\in\bigcup_nA_n\}
    =\bigcup_n\{g\in U:g\cdot x\in A_n\}
    $$
    is non-meager in $U$. A countable union is non-meager iff one term is non-meager, since countable unions of meager sets
    are meager. Hence
    $$
    \Big(\bigcup_n A_n\Big)^{*U}=\bigcup_n A_n^{*U}.
    $$
    The countable-intersection rule for $\triangle$ follows by applying duality to the preceding identity.
-/
theorem categoryStar_iUnion {X : Type*} (U : Set G) (R : ℕ → Set (G × X)) :
    categoryStar U (⋃ n, R n) = ⋃ n, categoryStar U (R n) := by
  ext x
  simp [categoryStar, relationSection, preimage_iUnion, iUnion_inter,
    isMeagre_iUnion_iff_book, not_forall]

theorem categoryTriangle_iInter {X : Type*} (U : Set G) (R : ℕ → Set (G × X)) :
    categoryTriangle U (⋂ n, R n) = ⋂ n, categoryTriangle U (R n) := by
  have h := congrArg compl (categoryStar_iUnion U (fun n => (R n)ᶜ))
  simpa only [categoryStar_compl, compl_iUnion, compl_compl] using h

theorem mem_categoryTriangle_local [BaireSpace G] {X : Type*}
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (R : Set (G × X)) (x : X) (hR : BaireMeasurableSet (relationSection R x)) :
    x ∈ categoryTriangle U R ↔
      ∀ V ∈ B, V.Nonempty → V ⊆ U → x ∈ categoryStar V R :=
  comeagre_iff_forall_basis_nonmeagre hB hR hU

theorem mem_categoryStar_local [BaireSpace G] {X : Type*}
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (R : Set (G × X)) (x : X) (hR : BaireMeasurableSet (relationSection R x)) :
    x ∈ categoryStar U R ↔
      ∃ V ∈ B, V.Nonempty ∧ V ⊆ U ∧ x ∈ categoryTriangle V R :=
  nonmeagre_iff_exists_basis_comeagre hB hR hU

/-- The localized union rule only needs the Baire property of each section. -/
theorem categoryTriangle_iUnion [BaireSpace G] {X : Type*}
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (R : ℕ → Set (G × X)) (hR : ∀ n x, BaireMeasurableSet (relationSection (R n) x)) :
    categoryTriangle U (⋃ n, R n) =
      ⋂ V ∈ B, ⋂ (_ : V.Nonempty), ⋂ (_ : V ⊆ U), ⋃ n, categoryStar V (R n) := by
  ext x
  have hb : BaireMeasurableSet (relationSection (⋃ n, R n) x) := by
    simpa only [relationSection, preimage_iUnion] using BaireMeasurableSet.iUnion (fun n => hR n x)
  rw [mem_categoryTriangle_local hB hU _ x hb]
  simp only [categoryStar_iUnion, mem_iInter]

/-- The localized intersection rule uses the same localization theorem. -/
theorem categoryStar_iInter [BaireSpace G] {X : Type*}
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (R : ℕ → Set (G × X)) (hR : ∀ n x, BaireMeasurableSet (relationSection (R n) x)) :
    categoryStar U (⋂ n, R n) =
      ⋃ V ∈ B, ⋃ (_ : V.Nonempty), ⋃ (_ : V ⊆ U), ⋂ n, categoryTriangle V (R n) := by
  ext x
  have hb : BaireMeasurableSet (relationSection (⋂ n, R n) x) := by
    simpa only [relationSection, preimage_iInter] using BaireMeasurableSet.iInter (fun n => hR n x)
  rw [mem_categoryStar_local hB hU _ x hb]
  simp only [categoryTriangle_iInter, mem_iUnion, exists_prop]

/-- An open section is nonmeager precisely when it is nonempty. -/
theorem categoryStar_open_eq [BaireSpace G] {X : Type*} [TopologicalSpace X]
    {U : Set G} (hU : IsOpen U) {R : Set (G × X)} (hR : IsOpen R) :
    categoryStar U R = {x | ∃ g ∈ U, (g, x) ∈ R} := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hgR, hgU⟩ := nonempty_of_not_isMeagre hx
    exact ⟨g, hgU, hgR⟩
  · rintro ⟨g, hgU, hgR⟩
    exact not_isMeagre_of_isOpen
      ((hR.preimage (continuous_id.prodMk continuous_const)).inter hU) ⟨g, hgR, hgU⟩

/-- The open projection is a union of its open slices at fixed group elements. -/
theorem isOpen_categoryStar [BaireSpace G] {X : Type*} [TopologicalSpace X]
    {U : Set G} (hU : IsOpen U) {R : Set (G × X)} (hR : IsOpen R) :
    IsOpen (categoryStar U R) := by
  rw [categoryStar_open_eq hU hR]
  have he : {x | ∃ g ∈ U, (g, x) ∈ R} = ⋃ g ∈ U, (fun x => (g, x)) ⁻¹' R := by
    ext x; simp
  rw [he]
  exact isOpen_iUnion fun g => isOpen_iUnion fun _ =>
    hR.preimage (continuous_const.prodMk continuous_id)

theorem categoryTriangle_eq_iInter [BaireSpace G] {X : Type*}
    {B : Set (Set G)} (hB : IsTopologicalBasis B) {U : Set G} (hU : IsOpen U)
    (R : Set (G × X)) (hR : ∀ x, BaireMeasurableSet (relationSection R x)) :
    categoryTriangle U R = ⋂ V ∈ B, ⋂ (_ : V.Nonempty), ⋂ (_ : V ⊆ U), categoryStar V R := by
  ext x
  rw [mem_categoryTriangle_local hB hU _ x (hR x)]
  simp only [mem_iInter]

/-- The comeager quantifier of an open relation is a countable intersection of open sets. -/
theorem isGdelta_categoryTriangle_open [BaireSpace G] {X : Type*} [TopologicalSpace X]
    {B : Set (Set G)} (hB : IsTopologicalBasis B) (hBc : B.Countable)
    {U : Set G} (hU : IsOpen U) {R : Set (G × X)} (hR : IsOpen R) :
    IsGδ (categoryTriangle U R) := by
  rw [categoryTriangle_eq_iInter hB hU R (fun _ =>
    (hR.preimage (continuous_id.prodMk continuous_const)).baireMeasurableSet)]
  apply IsGδ.biInter hBc
  intro V hVB
  exact IsGδ.iInter fun _ => IsGδ.iInter fun _ => (isOpen_categoryStar (hB.isOpen hVB) hR).isGδ

end PolishSpaceBook
