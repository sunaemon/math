module

public import PolishSpaceBook.LusinRankSeparation

@[expose] public section

/-!
# Disjoint and compatible Borel prefix tests

Separate each prefix image from the other images at its level, remove earlier
numerical word codes, and intersect the tests along nonempty prefixes.
-/

namespace PolishSpaceBook
namespace LusinSuslinPrefix

open Set TopologicalSpace Topology MeasureTheory NamedLambda

variable {Y : Type*} {F : Set baire_space}

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    If $F=\emptyset$, then both the image and inverse claims are immediate. Otherwise, take $F\IncludedIn\BaireSpace$
    closed and nonempty, let $f:F\to Y$ be continuous and injective, and fix a compatible metric $d_Y$ on $Y$. For each
    finite sequence $s\in\finseq{\omega}$ put
    $$
    A_s := f(F\cap\cyl{s}).
-/
def slice (f : F → Y) (s : List ℕ) : Set Y :=
  f '' {x | x.val ∈ cyl s}

theorem slices_disjoint {f : F → Y} (hf : Function.Injective f)
    {s t : List ℕ} (hne : s ≠ t) (hl : s.length = t.length) :
    Disjoint (slice f s) (slice f t) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
  have heq : z = x := hf he
  subst z
  apply hne
  rw [← seqPrefix_eq_of_mem_cyl hx, hl, seqPrefix_eq_of_mem_cyl hz]

section Topological

variable [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Each $A_s$ is analytic. For a fixed length $k\ge 1$, the family $\{A_s:s\in\funcspace{k}{\omega}\}$ is pairwise
    disjoint, because the cylinders of length $k$ are disjoint and $f$ is injective.
-/
theorem slice_analytic (hF : IsClosed F) {f : F → Y} (hf : Continuous f) (s : List ℕ) :
    AnalyticSet (slice f s) := by
  let : PolishSpace F := hF.polishSpace
  exact analyticSet_borel_image_via_refinement
    ((isOpen_cyl s).preimage continuous_subtype_val).measurableSet hf.measurable

/-- The raw separator contains one prefix image and misses every other image at its level. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    This union is disjoint from $A_s$.
    The \termuse{Lusin separation theorem} therefore gives a Borel set $C_s$ containing $A_s$ and disjoint from every
    $A_t$ with $|t|=|s|$ and $t\ne s$.
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Fix an injective numbering $\iota:\finseq{\omega}\to\omega$ of finite sequences. For each $s$, the union
    $$\bigcup_{\substack{|t|=|s|\\t\ne s}}A_t
-/
theorem exists_raw_tests (hF : IsClosed F) {f : F → Y}
    (hf : Continuous f) (hi : Function.Injective f) :
    ∃ C : List ℕ → Set Y, (∀ s, MeasurableSet (C s)) ∧
      (∀ s, slice f s ⊆ C s) ∧
      ∀ s t, s ≠ t → s.length = t.length → Disjoint (slice f s) (C t) := by
  classical
  let other (s : List ℕ) (j : ℕ) : Set Y :=
    if (NatListCode.decode j).length = s.length ∧ NatListCode.decode j ≠ s then
      slice f (NatListCode.decode j) else ∅
  have ha (s : List ℕ) : AnalyticSet (⋃ j, other s j) := by
    apply analyticSet_iUnion
    intro j
    dsimp [other]
    split_ifs
    · exact slice_analytic hF hf _
    · exact analyticSet_empty
  have hd (s : List ℕ) : Disjoint (slice f s) (⋃ j, other s j) := by
    apply disjoint_iUnion_right.mpr
    intro j
    dsimp [other]
    split_ifs with h
    · exact slices_disjoint hi (Ne.symm h.2) h.1.symm
    · exact disjoint_empty _
  choose C hsub hmiss hC using fun s => lusinSeparation_via_ranks (slice_analytic hF hf s) (ha s) (hd s)
  refine ⟨C, hC, hsub, ?_⟩
  intro s t hne hl
  apply Set.disjoint_left.mpr
  intro y hy hyt
  apply hmiss t hyt
  apply mem_iUnion.mpr
  refine ⟨NatListCode.encode s, ?_⟩
  simpa [other, hl, hne] using hy

end Topological

/-- Disjointification at one length, ordered by the numerical code of a word. -/
def disjointTest (C : List ℕ → Set Y) (s : List ℕ) : Set Y :=
  {y | y ∈ C s ∧ ∀ j < NatListCode.encode s,
    (NatListCode.decode j).length = s.length → y ∉ C (NatListCode.decode j)}

/-- Only positive prefix lengths occur in the book's compatibility test. -/
def compatibleTest (C : List ℕ → Set Y) (s : List ℕ) : Set Y :=
  {y | ∀ n, 0 < n → n ≤ s.length → y ∈ disjointTest C (s.take n)}

section Measurable

variable [MeasurableSpace Y]

theorem disjointTest_measurable {C : List ℕ → Set Y} (hC : ∀ s, MeasurableSet (C s)) (s : List ℕ) :
    MeasurableSet (disjointTest C s) := by
  have h := (hC s).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j < NatListCode.encode s) =>
    MeasurableSet.iInter fun (_ : (NatListCode.decode j).length = s.length) => (hC (NatListCode.decode j)).compl)
  convert h using 1
  ext y
  simp [disjointTest]

theorem compatibleTest_measurable {C : List ℕ → Set Y} (hC : ∀ s, MeasurableSet (C s)) (s : List ℕ) :
    MeasurableSet (compatibleTest C s) := by
  have h := MeasurableSet.iInter fun n => MeasurableSet.iInter fun (_ : 0 < n) =>
    MeasurableSet.iInter fun (_ : n ≤ s.length) => disjointTest_measurable hC (s.take n)
  convert h using 1
  ext y
  simp [compatibleTest]

end Measurable

theorem disjointTest_unique {C : List ℕ → Set Y} {s t : List ℕ} {y : Y}
    (hs : y ∈ disjointTest C s) (ht : y ∈ disjointTest C t) (hl : s.length = t.length) : s = t := by
  rcases lt_trichotomy (NatListCode.encode s) (NatListCode.encode t) with h | h | h
  · exact False.elim (ht.2 _ h (by simpa only [NatListCode.decode_encode] using hl)
      (by simpa only [NatListCode.decode_encode] using hs.1))
  · simpa only [NatListCode.decode_encode] using congrArg NatListCode.decode h
  · exact False.elim (hs.2 _ h (by simpa only [NatListCode.decode_encode] using hl.symm)
      (by simpa only [NatListCode.decode_encode] using ht.1))

theorem compatibleTest_take {C : List ℕ → Set Y} {s : List ℕ} {y : Y}
    (hs : y ∈ compatibleTest C s) (n : ℕ) : y ∈ compatibleTest C (s.take n) := by
  intro k hk hks
  have hkn : k ≤ n := (by simpa only [List.length_take] using hks : k ≤ min n s.length).trans (min_le_left _ _)
  have hkl : k ≤ s.length := (by simpa only [List.length_take] using hks : k ≤ min n s.length).trans (min_le_right _ _)
  simpa only [List.take_take, min_eq_left hkn] using hs k hk hkl

theorem compatibleTest_unique {C : List ℕ → Set Y} {s t : List ℕ} {y : Y}
    (hs : y ∈ compatibleTest C s) (ht : y ∈ compatibleTest C t) (hl : s.length = t.length) : s = t := by
  by_cases hz : s.length = 0
  · have hs0 : s = [] := by simpa using hz
    have ht0 : t = [] := by simpa using (hl.symm.trans hz)
    exact hs0.trans ht0.symm
  · apply disjointTest_unique (C := C) (y := y) _ _ hl
    · simpa only [List.take_length] using hs s.length (Nat.pos_of_ne_zero hz) le_rfl
    · simpa only [List.take_length] using ht t.length (by omega) le_rfl

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    For $|s|=k\ge1$, put
    $$B_s^k:=\SetDifference{C_s}{\bigcup_{\substack{|t|=k\\\iota(t)<\iota(s)}}C_t}.$$
    Only finitely many terms occur in this union, since $\iota$ is injective. No removed set meets $A_s$, so
    $A_s\IncludedIn B_s^k$. The sets $B_s^k$ are pairwise disjoint at each fixed level: if
    $\iota(s)<\iota(t)$, then $B_t^k$ misses $C_s$, which contains $B_s^k$. All these sets are Borel.
-/
theorem slice_subset_disjointTest {f : F → Y} {C : List ℕ → Set Y}
    (hsub : ∀ s, slice f s ⊆ C s)
    (hdisj : ∀ s t, s ≠ t → s.length = t.length → Disjoint (slice f s) (C t)) (s : List ℕ) :
    slice f s ⊆ disjointTest C s := by
  intro y hy
  refine ⟨hsub s hy, ?_⟩
  intro j hj hl hc
  have hne : s ≠ NatListCode.decode j := by
    intro he
    have hh := congrArg NatListCode.encode he
    rw [NatListCode.encode_decode] at hh
    omega
  exact Set.disjoint_left.mp (hdisj s _ hne hl.symm) hy hc

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Make the tests compatible along prefixes by setting, for $|s|=k\ge 1$,
    $$
    H_s := \bigcap_{1\le j\le k} B_{\restrict{s}{j}}^j.
    $$
    Then $A_s\IncludedIn H_s$, the sets $H_s$ at a fixed level are pairwise disjoint, and $t\extendsPrefix s$ implies
    $H_t\IncludedIn H_s$.
-/
theorem slice_subset_compatibleTest {f : F → Y} {C : List ℕ → Set Y}
    (hsub : ∀ s, slice f s ⊆ C s)
    (hdisj : ∀ s t, s ≠ t → s.length = t.length → Disjoint (slice f s) (C t)) (s : List ℕ) :
    slice f s ⊆ compatibleTest C s := by
  rintro y ⟨x, hx, rfl⟩ n _ _
  apply slice_subset_disjointTest hsub hdisj
  exact ⟨x, prefixOfSeq_of_prefix (List.take_prefix n s) hx, rfl⟩

end LusinSuslinPrefix
end PolishSpaceBook
