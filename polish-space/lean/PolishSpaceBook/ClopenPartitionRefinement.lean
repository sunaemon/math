module

public import PolishSpaceBook.PolishSpaces

@[expose] public section

/-! # Disjointifying countable clopen covers in their enumeration order -/
namespace PolishSpaceBook
open Set TopologicalSpace
universe u
variable {X : Type u} [TopologicalSpace X]

/-- The nth piece removes exactly the earlier members of a countable cover. -/
def clopenPartitionPiece (C : ℕ → Set X) (n : ℕ) : Set X :=
  C n \ ⋃ j ∈ Finset.range n, C j

theorem clopenPartitionPiece_clopen (C : ℕ → Set X) (hC : ∀ n, IsClopen (C n)) (n : ℕ) :
    IsClopen (clopenPartitionPiece C n) :=
  (hC n).diff (isClopen_biUnion_finset (fun j _ => hC j))

omit [TopologicalSpace X] in
theorem clopenPartitionPiece_disjoint (C : ℕ → Set X) :
    Pairwise (fun n m => Disjoint (clopenPartitionPiece C n) (clopenPartitionPiece C m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hy.2 (mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hlt, hx.1⟩)
  · exact hx.2 (mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr hgt, hy.1⟩)

omit [TopologicalSpace X] in
/-- The first covering index places each point in one of the disjoint pieces. -/
theorem clopenPartitionPiece_cover (C : ℕ → Set X) (hc : (⋃ n, C n) = univ) :
    (⋃ n, clopenPartitionPiece C n) = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  have h : ∃ n, x ∈ C n := mem_iUnion.mp (hc ▸ mem_univ x)
  refine mem_iUnion.mpr ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
  exact Nat.find_min h (Finset.mem_range.mp hj) hxj

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Suppose $X$ has a clopen base. Separability and metrizability imply second countability. A second-countable space,
    and each of its open subspaces, is Lindelöf: from any open cover, for each basic open set contained in some member of
    the cover, choose one such member. Cover each member of a countable base by clopen subsets and choose a countable
    subcover.
    Taking these subcovers together gives a countable clopen base.
-/
/-- Cover each member of a fixed countable basis by countably many clopen sets,
then take the union of those subcovers. -/
theorem countable_clopen_basis_by_subcovers [SecondCountableTopology X]
    (hz : IsZeroDimensional X) :
    ∃ B : ℕ → Set X, (∀ n, IsClopen (B n)) ∧ IsTopologicalBasis (range B) := by
  classical
  have hsub : ∀ U ∈ countableBasis X, ∃ s ⊆ {V : Set X | IsClopen V},
      s.Countable ∧ U = ⋃ V ∈ s, V := fun U hU =>
    hz.exists_countable_biUnion_of_isOpen ((isBasis_countableBasis X).isOpen hU)
  choose s hs hsc hcover using hsub
  let t : Set (Set X) := ⋃ U : countableBasis X, s U.val U.property
  have htc : t.Countable := countable_iUnion (fun U => hsc U.val U.property)
  have htcl : ∀ V ∈ t, IsClopen V := by
    intro V hV
    obtain ⟨U, hV⟩ := mem_iUnion.mp hV
    exact hs U.val U.property hV
  have htb : IsTopologicalBasis t := by
    apply isTopologicalBasis_of_isOpen_of_nhds (fun V hV => (htcl V hV).isOpen)
    intro x O hx hO
    obtain ⟨U, hU, hxU, hUO⟩ :=
      (isBasis_countableBasis X).exists_subset_of_mem_open hx hO
    obtain ⟨V, hVs, hxV⟩ := mem_iUnion₂.mp ((hcover U hU) ▸ hxU)
    refine ⟨V, mem_iUnion.mpr ⟨⟨U, hU⟩, hVs⟩, hxV, ?_⟩
    intro y hy
    apply hUO
    rw [hcover U hU]
    exact mem_iUnion₂.mpr ⟨V, hVs, hy⟩
  obtain ⟨B, hB⟩ := (htc.insert ∅).exists_eq_range (insert_nonempty ∅ t)
  refine ⟨B, ?_, ?_⟩
  · intro n
    rcases (hB ▸ mem_range_self n : B n ∈ insert ∅ t) with he | ht
    · exact he ▸ isClopen_empty
    · exact htcl _ ht
  · rw [← hB]
    apply isTopologicalBasis_of_isOpen_of_nhds
      (fun V hV => hV.elim (fun he => he ▸ isOpen_empty) (fun ht => (htcl _ ht).isOpen))
    intro x O hx hO
    obtain ⟨V, hV, hxV, hVO⟩ := htb.exists_subset_of_mem_open hx hO
    exact ⟨V, mem_insert_of_mem _ hV, hxV, hVO⟩

/-- Retain the clopen basis members subordinate to the open cover, adding the empty
set to make an enumeration possible even when X is empty. -/
theorem exists_subordinate_countable_clopen_cover [SecondCountableTopology X]
    (hz : IsZeroDimensional X) {I : Type} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hc : (⋃ i, U i) = univ) :
    ∃ C : ℕ → Set X, (∀ n, IsClopen (C n)) ∧ (⋃ n, C n) = univ ∧
      ∀ n, ∃ i, C n ⊆ U i := by
  classical
  obtain ⟨B, hB, hb⟩ := countable_clopen_basis_by_subcovers hz
  let s : Set (Set X) := {V | V ∈ range B ∧ ∃ i, V ⊆ U i}
  have hs : s.Countable := (countable_range B).mono (fun _ h => h.1)
  obtain ⟨C, he⟩ := (hs.insert ∅).exists_eq_range (insert_nonempty ∅ s)
  have hCs : ∀ n, C n ∈ insert ∅ s := fun n => he ▸ mem_range_self n
  refine ⟨C, ?_, ?_, ?_⟩
  · intro n
    rcases hCs n with he | ⟨⟨k, hk⟩, _⟩
    · exact he ▸ isClopen_empty
    · exact hk ▸ hB k
  · apply eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hc ▸ mem_univ x)
    obtain ⟨V, hV, hxV, hVU⟩ := hb.exists_subset_of_mem_open hxi (hU i)
    have hVs : V ∈ insert ∅ s := mem_insert_of_mem _ ⟨hV, i, hVU⟩
    obtain ⟨n, hn⟩ := he ▸ hVs
    exact mem_iUnion.mpr ⟨n, hn ▸ hxV⟩
  · intro n
    rcases hCs n with he | ⟨_, i, hi⟩
    · exact ⟨Classical.choice inferInstance, he ▸ empty_subset _⟩
    · exact ⟨i, hi⟩

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Let $\mathcal U$ be any open cover. Enumerate the members of this clopen base that are contained in some member of
    $\mathcal U$ as $C_0,C_1,\ldots$, allowing repetitions if the family is finite. They cover $X$. Put
    $$D_n:=\SetDifference{C_n}{\bigcup_{j<n}C_j}.$$
    The sets $D_n$ are clopen, pairwise disjoint, and cover $X$: each point $x$ belongs to $D_n$ for the
    least $n$ with $x\in C_n$. Moreover, each $D_n$ lies in some member of $\mathcal U$.
-/
/-- A disjoint clopen partition refining an arbitrary open cover. -/
theorem exists_clopen_partition_refinement [SecondCountableTopology X]
    (hz : IsZeroDimensional X) {I : Type} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hc : (⋃ i, U i) = univ) :
    ∃ D : ℕ → Set X, (∀ n, IsClopen (D n)) ∧ (⋃ n, D n) = univ ∧
      Pairwise (fun n m => Disjoint (D n) (D m)) ∧ ∀ n, ∃ i, D n ⊆ U i := by
  obtain ⟨C, hC, hCc, hr⟩ := exists_subordinate_countable_clopen_cover hz U hU hc
  refine ⟨clopenPartitionPiece C, clopenPartitionPiece_clopen C hC,
    clopenPartitionPiece_cover C hCc, clopenPartitionPiece_disjoint C, ?_⟩
  intro n
  obtain ⟨i, hi⟩ := hr n
  exact ⟨i, fun _ hx => hi hx.1⟩

/-- Every subunion of a disjoint open partition is clopen: its complement is the
union of the unselected pieces. -/
theorem clopen_partition_subunion (D : ℕ → Set X) (hD : ∀ n, IsOpen (D n))
    (hc : (⋃ n, D n) = univ) (hd : Pairwise (fun n m => Disjoint (D n) (D m)))
    (s : Set ℕ) : IsClopen (⋃ n : s, D n.val) := by
  have he : (⋃ n : s, D n.val)ᶜ = ⋃ n : {n : ℕ // n ∉ s}, D n.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp (hc ▸ mem_univ x)
      have hn : n ∉ s := fun hn => hx (mem_iUnion.mpr ⟨⟨n, hn⟩, hxn⟩)
      exact mem_iUnion.mpr ⟨⟨n, hn⟩, hxn⟩
    · intro hx hy
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hy
      have hnm : n.val ≠ m.val := fun he => n.property (he ▸ m.property)
      exact Set.disjoint_left.mp (hd hnm) hxn hxm
  exact ⟨isOpen_compl_iff.mp (he ▸ isOpen_iUnion (fun n => hD n.val)),
    isOpen_iUnion (fun n => hD n.val)⟩

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Given a closed set $F\IncludedIn U$ with $U$ open, apply this construction to
    $\{U,\SetDifference{X}{F}\}$. The union
    $$V:=\bigcup\{D_n:D_n\cap F\ne\emptyset\}$$
    is contained in $U$ and contains $F$. It is clopen because both it and its complement are unions of members of the
    partition. Thus $\LargeInductiveDimension{X}\le 0$.
-/
/-- Select exactly the partition pieces that meet the closed set. -/
theorem IsZeroDimensional.hasBigInductiveDimensionLEZero_by_partition
    [SecondCountableTopology X] (hz : IsZeroDimensional X) :
    HasBigInductiveDimensionLEZero X := by
  classical
  intro F U hF hU hFU
  let C : Bool → Set X := fun b => if b then U else Fᶜ
  have hCo : ∀ b, IsOpen (C b) := by intro b; cases b <;> simp [C, hU, hF.isOpen_compl]
  have hCc : (⋃ b, C b) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ U
    · exact mem_iUnion.mpr ⟨true, hx⟩
    · exact mem_iUnion.mpr ⟨false, fun hxF => hx (hFU hxF)⟩
  obtain ⟨D, hD, hDc, hd, hr⟩ := exists_clopen_partition_refinement hz C hCo hCc
  let s : Set ℕ := {n | (D n ∩ F).Nonempty}
  refine ⟨⋃ n : s, D n.val,
    clopen_partition_subunion D (fun n => (hD n).isOpen) hDc hd s, ?_, ?_⟩
  · intro x hxF
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (hDc ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨⟨n, x, hxn, hxF⟩, hxn⟩
  · intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := hr n.val
    cases b with
    | true => exact hb hxn
    | false =>
      obtain ⟨y, hyD, hyF⟩ := n.property
      exact ((hb hyD) hyF).elim

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    For a finite open cover $U_1,\ldots,U_r$, choose for each $n$ an index $i(n)$ with $D_n\IncludedIn U_{i(n)}$ and set
    $$V_i:=\bigcup_{i(n)=i}D_n\qquad(1\le i\le r).$$
    These sets form a finite pairwise disjoint open refinement. Hence $\CoveringDimension{X}\le 0$.
-/
/-- Regroup the countable disjoint pieces by the chosen original-cover index. -/
theorem IsZeroDimensional.hasCoveringDimensionLEZero_by_partition
    [SecondCountableTopology X] (hz : IsZeroDimensional X) :
    HasCoveringDimensionLEZero X := by
  classical
  intro I _ U hU hc
  by_cases hi : Nonempty I
  · let := hi
    obtain ⟨D, hD, hDc, hd, hr⟩ := exists_clopen_partition_refinement hz U hU hc
    choose a ha using hr
    let V : I → Set X := fun i => ⋃ n : {n : ℕ // a n = i}, D n.val
    refine ⟨V, fun i => isOpen_iUnion (fun n => (hD n.val).isOpen), ?_, ?_, ?_⟩
    · apply eq_univ_of_forall
      intro x
      obtain ⟨n, hxn⟩ := mem_iUnion.mp (hDc ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨a n, mem_iUnion.mpr ⟨⟨n, rfl⟩, hxn⟩⟩
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hxi
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hxj
      have hnm : n.val ≠ m.val := by
        intro he
        exact hij (n.property.symm.trans ((congrArg a he).trans m.property))
      exact Set.disjoint_left.mp (hd hnm) hxn hxm
    · intro i x hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      exact n.property ▸ ha n.val hxn
  · have : IsEmpty I := not_nonempty_iff.mp hi
    exact ⟨U, hU, hc, fun i => isEmptyElim i, fun _ => subset_rfl⟩

end PolishSpaceBook
