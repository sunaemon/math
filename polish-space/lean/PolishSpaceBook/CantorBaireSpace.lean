module

public import PolishSpaceBook.PolishSpaces
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.Disjointed
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Cantor space and Baire space

Formalization targets for `polish-space/src/polish-space-book/cantor-baire-space.md`.
-/

namespace PolishSpaceBook

universe u

open Set TopologicalSpace Topology

/-
The first section of the chapter fixes the common prefix language for
Cantor space and Baire space.  In Lean we use `List A` for finite words
over an alphabet `A`, and functions `ℕ → A` for infinite sequences.
-/

section PrefixLanguage

variable {A : Type u}

/-!
## Prefix language

| Book notation | Lean name |
| --- | --- |
| `\finseq{A}` | `finseq A` |
| `s \concat t` | `concat s t` |
| `s \prefixOf t` for finite words | `prefixOf s t` |
| `s \prefixOf x` for an infinite sequence | `prefixOfSeq s x` |
| `s \properPrefixOf t` | `properPrefixOf s t` |
| `t \extendsPrefix s` | `extendsPrefix t s` |
| `\wordRepeat{w}{n}` | `wordRepeat w n` |
-/

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    We write $\finseq{A} = \bigcup_{n \in \omega} \seqPower{A}{n}$ for finite sequences with entries in $A$. If $s \in
    \seqPower{A}{n}$, then $|s| := n$; the empty sequence $\emptySeq$ is the unique element of $\seqPower{A}{0}$. For a
    finite sequence $s$ and a finite or infinite sequence $t$ with matching entries, $s \concat t$ denotes concatenation.
-/
/-- Book notation `\finseq{A}`: finite words over the alphabet `A`. -/
abbrev finseq (A : Type u) : Type u :=
  List A

/-- The finite prefix of length `n` of an infinite sequence. -/
def seqPrefix (x : ℕ → A) (n : ℕ) : finseq A :=
  List.ofFn fun i : Fin n => x i

/-- Book notation `s \concat t`: concatenation of finite words. -/
abbrev concat (s t : finseq A) : finseq A :=
  s ++ t

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The prefix relation $s\prefixOf y$ means that the finite sequence $s$ is an initial segment of $y$, where $y$ may be
    finite or infinite. We write $s\notPrefixOf y$ for its negation, $s\properPrefixOf y$ for proper prefix, and
    $t\extendsPrefix s$ when $t$ extends $s$.
-/
/-- Book notation `s \prefixOf t` when both words are finite. -/
abbrev prefixOf (s t : finseq A) : Prop :=
  s <+: t

/-- Book notation `s \notPrefixOf t` when both words are finite. -/
abbrev notPrefixOf (s t : finseq A) : Prop :=
  ¬ prefixOf s t

/-- Book notation `s \properPrefixOf t` when both words are finite. -/
abbrev properPrefixOf (s t : finseq A) : Prop :=
  prefixOf s t ∧ s.length < t.length

/-- Book notation `t \extendsPrefix s`: the finite word `t` extends `s`. -/
abbrev extendsPrefix (t s : finseq A) : Prop :=
  prefixOf s t

/-- Book notation `s \prefixOf x` for a finite word and an infinite sequence. -/
def prefixOfSeq (s : finseq A) (x : ℕ → A) : Prop :=
  ∀ i (hi : i < s.length), x i = s.get ⟨i, hi⟩

/-- Book notation `s \notPrefixOf x` for a finite word and an infinite sequence. -/
abbrev notPrefixOfSeq (s : finseq A) (x : ℕ → A) : Prop :=
  ¬ prefixOfSeq s x

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    For a finite word or symbol $w$ and $n\in\omega$, $\wordRepeat{w}{n}$ is the concatenation of $n$ copies of $w$.
    For $n=0$, the result is the empty word $\emptySeq$.
-/
/-- Book notation `\wordRepeat{w}{n}` for repeating a finite word `w`, `n` times. -/
def wordRepeat (w : finseq A) : ℕ → finseq A
  | 0 => []
  | n + 1 => wordRepeat w n ++ w

@[simp]
theorem prefixOfSeq_nil (x : ℕ → A) :
    prefixOfSeq ([] : finseq A) x := by
  intro i hi
  cases hi

@[simp]
theorem prefixOfSeq_singleton {a : A} {x : ℕ → A} :
    prefixOfSeq ([a] : finseq A) x ↔ x 0 = a := by
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h i hi
    have hi0 : i = 0 := by
      have hi' : i < 1 := by simpa using hi
      omega
    subst hi0
    simpa using h

@[simp]
theorem seqPrefix_length (x : ℕ → A) (n : ℕ) :
    (seqPrefix x n).length = n := by
  simp [seqPrefix]

theorem seqPrefix_get (x : ℕ → A) {n i : ℕ} (hi : i < (seqPrefix x n).length) :
    (seqPrefix x n).get ⟨i, hi⟩ = x i := by
  simp [seqPrefix]

theorem prefixOfSeq_seqPrefix (x : ℕ → A) (n : ℕ) :
    prefixOfSeq (seqPrefix x n) x := by
  intro i hi
  exact (seqPrefix_get x hi).symm

theorem prefixOfSeq_of_concat {s t : finseq A} {x : ℕ → A}
    (h : prefixOfSeq (concat s t) x) :
    prefixOfSeq s x := by
  intro i hi
  have hconcat : i < (concat s t).length := by
    simpa [concat] using lt_of_lt_of_le hi (Nat.le_add_right s.length t.length)
  simpa [concat, List.getElem_append, hi] using h i hconcat

theorem seqPrefix_prefixOf_of_le (x : ℕ → A) {n m : ℕ} (hnm : n ≤ m) :
    prefixOf (seqPrefix x n) (seqPrefix x m) := by
  change seqPrefix x n <+: seqPrefix x m
  rw [List.prefix_iff_getElem]
  refine ⟨by simpa [seqPrefix_length] using hnm, ?_⟩
  intro i hi
  simp [seqPrefix]

theorem seqPrefix_succ_eq_concat (x : ℕ → A) (n : ℕ) :
    seqPrefix x (n + 1) = concat (seqPrefix x n) [x n] := by
  unfold seqPrefix concat
  rw [List.ofFn_succ']
  simp

theorem seqPrefix_take_of_le (x : ℕ → A) {m n : ℕ} (hmn : m ≤ n) :
    (seqPrefix x n).take m = seqPrefix x m := by
  apply List.ext_get
  · simp [seqPrefix, hmn]
  · intro i hi htake
    simp [seqPrefix]

@[simp]
theorem wordRepeat_zero (w : finseq A) :
    wordRepeat w 0 = [] :=
  rfl

@[simp]
theorem wordRepeat_succ (w : finseq A) (n : ℕ) :
    wordRepeat w (n + 1) = wordRepeat w n ++ w :=
  rfl

end PrefixLanguage

section Cylinders

variable {A : Type u}

/-!
## Cylinders

| Book notation | Lean name |
| --- | --- |
| `\cyl{s}` | `cyl s` |
-/

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    For a
    finite sequence $s\in\finseq{A}$, the \termdefine{cylinder} determined by $s$ is
    $$
    \cyl{s}:=\{x\in A^\omega:s\prefixOf x\}.
    $$
-/
/-- Book notation `\cyl{s}`: infinite sequences extending the finite word `s`. -/
def cyl (s : finseq A) : Set (ℕ → A) :=
  {x | prefixOfSeq s x}

@[simp]
theorem mem_cyl {s : finseq A} {x : ℕ → A} :
    x ∈ cyl s ↔ prefixOfSeq s x :=
  Iff.rfl

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\SeqMetricName$ is a metric on both $\CantorSpace$ and $\BaireSpace$, and in each case $\SeqMetricName$ is compatible with the
-/
@[simp]
theorem cyl_nil :
    cyl ([] : finseq A) = (Set.univ : Set (ℕ → A)) := by
  ext x
  simp [cyl]

theorem cyl_concat_subset (s t : finseq A) :
    cyl (concat s t) ⊆ cyl s := by
  intro x hx
  exact prefixOfSeq_of_concat (x := x) hx

theorem mem_cyl_concat_iff {s t : finseq A} {x : ℕ → A} :
    x ∈ cyl (concat s t) ↔
      x ∈ cyl s ∧ (fun n : ℕ => x (s.length + n)) ∈ cyl t := by
  constructor
  · intro hx
    refine ⟨cyl_concat_subset s t hx, ?_⟩
    intro i hi
    have hidx : s.length + i < (concat s t).length := by
      simp [concat, hi]
    calc
      x (s.length + i) = (concat s t).get ⟨s.length + i, hidx⟩ := hx (s.length + i) hidx
      _ = t.get ⟨i, hi⟩ := by simp [concat]
  · rintro ⟨hxs, hxtail⟩ i hi
    by_cases his : i < s.length
    · simpa [concat, his] using hxs i his
    · have hle : s.length ≤ i := le_of_not_gt his
      let j : ℕ := i - s.length
      have hj : j < t.length := by
        have hi_len : i < s.length + t.length := by
          simpa [concat] using hi
        omega
      have hi_eq : s.length + j = i := by omega
      have hget : (concat s t).get ⟨i, hi⟩ = t.get ⟨j, hj⟩ := by
        simpa [concat, j] using
          (List.getElem_append_right (as := s) (bs := t) (i := i) hle)
      calc
        x i = x (s.length + j) := by rw [hi_eq]
        _ = t.get ⟨j, hj⟩ := hxtail j hj
        _ = (concat s t).get ⟨i, hi⟩ := hget.symm

theorem mem_cyl_seqPrefix (x : ℕ → A) (n : ℕ) :
    x ∈ cyl (seqPrefix x n) :=
  prefixOfSeq_seqPrefix x n

theorem seqPrefix_eq_of_mem_cyl {s : finseq A} {x : ℕ → A} (hx : x ∈ cyl s) :
    seqPrefix x s.length = s := by
  apply List.ext_get
  · simp
  · intro i hi hs
    calc
      (seqPrefix x s.length).get ⟨i, hi⟩ = x i := seqPrefix_get x hi
      _ = s.get ⟨i, hs⟩ := hx i hs

theorem prefixOfSeq_of_prefix {s t : finseq A} (hst : prefixOf s t) {x : ℕ → A}
    (hx : prefixOfSeq t x) :
    prefixOfSeq s x := by
  intro i hi
  have ht : i < t.length := lt_of_lt_of_le hi hst.length_le
  calc
    x i = t.get ⟨i, ht⟩ := hx i ht
    _ = s.get ⟨i, hi⟩ := by
      exact (hst.getElem hi).symm

theorem cyl_subset_of_prefix {s t : finseq A} (hst : prefixOf s t) :
    cyl t ⊆ cyl s := by
  intro x hx
  exact prefixOfSeq_of_prefix hst hx

theorem prefixOf_iff_exists_take {s t : finseq A} :
    prefixOf s t ↔ ∃ n : ℕ, n ≤ t.length ∧ s = t.take n := by
  constructor
  · intro hst
    exact ⟨s.length, hst.length_le, (List.prefix_iff_eq_take.mp hst)⟩
  · rintro ⟨n, hn, rfl⟩
    exact List.take_prefix n t

/-- An infinite sequence extending a finite word, filled afterwards by a default value. -/
noncomputable def extendFinseq [Inhabited A] (s : finseq A) : ℕ → A :=
  fun i => if hi : i < s.length then s.get ⟨i, hi⟩ else default

theorem seqPrefix_extendFinseq_of_le [Inhabited A] (s : finseq A)
    {n : ℕ} (hn : n ≤ s.length) :
    seqPrefix (extendFinseq s) n = s.take n := by
  apply List.ext_get
  · simp [seqPrefix, hn]
  · intro i hi htake
    have hi_n : i < n := by simpa [seqPrefix] using hi
    have hi_s : i < s.length := lt_of_lt_of_le hi_n hn
    simp [seqPrefix, extendFinseq, hi_s]

theorem extendFinseq_mem_cyl [Inhabited A] (s : finseq A) :
    extendFinseq s ∈ cyl s := by
  intro i hi
  simp [extendFinseq, hi]

theorem cyl_nonempty [Inhabited A] (s : finseq A) :
    (cyl s).Nonempty :=
  ⟨extendFinseq s, extendFinseq_mem_cyl s⟩

theorem prefixOf_of_cyl_subset [Nontrivial A] {s t : finseq A}
    (h : cyl t ⊆ cyl s) :
    prefixOf s t := by
  classical
  by_cases hlen : s.length ≤ t.length
  · change s <+: t
    rw [List.prefix_iff_getElem]
    let : Inhabited A := Classical.inhabited_of_nonempty inferInstance
    let x : ℕ → A := extendFinseq t
    have hxt : x ∈ cyl t := extendFinseq_mem_cyl t
    have hxs : x ∈ cyl s := h hxt
    refine ⟨hlen, ?_⟩
    intro i hi
    have hit : i < t.length := lt_of_lt_of_le hi hlen
    calc
      s[i] = x i := (hxs i hi).symm
      _ = t[i] := by simp [x, extendFinseq, hit]
  · have hlt : t.length < s.length := Nat.lt_of_not_ge hlen
    let : Inhabited A := Classical.inhabited_of_nonempty inferInstance
    obtain ⟨b, hb⟩ := exists_ne (s.get ⟨t.length, hlt⟩)
    let x : ℕ → A :=
      fun i => if hi : i < t.length then t.get ⟨i, hi⟩
        else if i = t.length then b else default
    have hxt : x ∈ cyl t := by
      intro i hi
      simp [x, hi]
    have hxs : x ∈ cyl s := h hxt
    have hxcoord := hxs t.length hlt
    have hxval : x t.length = b := by
      simp [x]
    exact False.elim (hb (by
      calc
        b = x t.length := hxval.symm
        _ = s.get ⟨t.length, hlt⟩ := hxcoord))

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The cylinders under reverse inclusion give the same tree:
    $$
    \begin{aligned}
    (\finseq{A},\prefixOf)
    &\xrightarrow{\;\sim\;}
    (\{\cyl{s}:s\in\finseq{A}\},\supseteq),\\
    s&\mapsto\cyl{s}.
    \end{aligned}
    $$
-/
theorem cyl_subset_iff_prefix [Nontrivial A] {s t : finseq A} :
    cyl t ⊆ cyl s ↔ prefixOf s t :=
  ⟨prefixOf_of_cyl_subset, cyl_subset_of_prefix⟩

theorem cyl_injective [Nontrivial A] :
    Function.Injective (fun s : finseq A => cyl s) := by
  intro s t hst
  change cyl s = cyl t at hst
  have hst' : prefixOf s t := (cyl_subset_iff_prefix (A := A)).1 (by rw [← hst])
  have hts' : prefixOf t s := (cyl_subset_iff_prefix (A := A)).1 (by rw [hst])
  exact hst'.eq_of_length_le hts'.length_le

theorem cyl_seqPrefix_eq_pinat (x : ℕ → A) (n : ℕ) :
    cyl (seqPrefix x n) = PiNat.cylinder x n := by
  ext y
  constructor
  · intro hy i hi
    have hlen : i < (seqPrefix x n).length := by simpa using hi
    calc
      y i = (seqPrefix x n).get ⟨i, hlen⟩ := hy i hlen
      _ = x i := seqPrefix_get x hlen
  · intro hy i hi
    calc
      y i = x i := hy i (by simpa using hi)
      _ = (seqPrefix x n).get ⟨i, hi⟩ := (seqPrefix_get x hi).symm

theorem cyl_eq_iInter (s : finseq A) :
    cyl s = ⋂ i : Fin s.length, {x : ℕ → A | x i = s.get i} := by
  ext x
  constructor
  · intro hx
    simp [cyl, prefixOfSeq] at hx ⊢
    intro i
    exact hx i i.2
  · intro hx i hi
    have hcoord : x (⟨i, hi⟩ : Fin s.length) = s.get ⟨i, hi⟩ := by
      simpa using Set.mem_iInter.mp hx ⟨i, hi⟩
    simpa using hcoord

theorem isClopen_cyl [TopologicalSpace A] [DiscreteTopology A] (s : finseq A) :
    IsClopen (cyl s : Set (ℕ → A)) := by
  classical
  rw [cyl_eq_iInter]
  exact isClopen_iInter_of_finite fun i =>
    (isClopen_discrete ({s.get i} : Set A)).preimage (continuous_apply (i : ℕ))

theorem isOpen_cyl [TopologicalSpace A] [DiscreteTopology A] (s : finseq A) :
    IsOpen (cyl s : Set (ℕ → A)) :=
  (isClopen_cyl s).isOpen

theorem isClosed_cyl [TopologicalSpace A] [DiscreteTopology A] (s : finseq A) :
    IsClosed (cyl s : Set (ℕ → A)) :=
  (isClopen_cyl s).isClosed

theorem finseq_countable [Countable A] :
    Countable (finseq A) := by
  infer_instance

theorem cylinder_family_countable [Countable A] :
    Set.Countable ({U : Set (ℕ → A) | ∃ s : finseq A, U = cyl s}) := by
  classical
  refine (Set.countable_range (fun s : finseq A => cyl s)).mono ?_
  rintro U ⟨s, rfl⟩
  exact ⟨s, rfl⟩

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The cylinders form the \termdefineas{standard base}{standard countable base} for the product topology in both cases.
    Indeed, $\finseq{A}$ is countable, since it is a countable union of finite powers of the countable alphabet $A$. Each
    cylinder is product-open because
    $$
    \cyl{s}=\bigcap_{i<|s|}\pi_i^{-1}(\{s_i\}),
    $$
    where $\pi_i:A^\omega\to A$ is the $i$-th coordinate projection and $A$ is discrete. Conversely, a basic product
    neighborhood of $x$ restricts only finitely many coordinates. If those coordinates lie below $n$, then
    $\cyl{\restrict{x}{n}}$ contains $x$ and is contained in that neighborhood. Thus every product-open set is a union of
    cylinders.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This appendix extends the numerical lambda calculus of §{sec:appendix-lambda-computability} to computation with
    an arbitrary input name. Baire space consists of the functions $\NN\to\NN$, with the product topology obtained
    from discrete $\NN$. An input name is supplied as a function argument; it need not be computable or finitely described.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a finite sequence $s$, write $\cyl{s}$ for the set of all names beginning with $s$. These prefix cylinders form a
    basis for the product topology on Baire space.
-/
theorem isTopologicalBasis_cyl [TopologicalSpace A] [DiscreteTopology A] :
    IsTopologicalBasis ({U : Set (ℕ → A) | ∃ s : finseq A, U = cyl s}) := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨s, rfl⟩
    exact isOpen_cyl s
  · intro x U hx hU
    obtain ⟨I, V, hxV, hVU⟩ := isOpen_pi_iff.mp hU x hx
    let n := I.sup id + 1
    refine ⟨cyl (seqPrefix x n), ⟨seqPrefix x n, rfl⟩, mem_cyl_seqPrefix x n, ?_⟩
    intro y hy
    apply hVU
    intro i hi
    have hin : i < n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    have hlen : i < (seqPrefix x n).length := by simpa using hin
    have heq : y i = x i := (hy i hlen).trans (seqPrefix_get x hlen)
    rw [heq]
    exact (hxV i hi).2

theorem exists_cyl_subset_of_mem_open [TopologicalSpace A] [DiscreteTopology A]
    {U : Set (ℕ → A)} {x : ℕ → A} (hx : x ∈ U) (hU : IsOpen U) :
    ∃ s : finseq A, x ∈ cyl s ∧ cyl s ⊆ U := by
  obtain ⟨V, ⟨s, rfl⟩, hxV, hVU⟩ :=
    (isTopologicalBasis_cyl (A := A)).exists_subset_of_mem_open hx hU
  exact ⟨s, hxV, hVU⟩

theorem exists_mem_cyl_ne [Nontrivial A] (s : finseq A) (x : ℕ → A) :
    ∃ y : ℕ → A, y ∈ cyl s ∧ y ≠ x := by
  obtain ⟨a, ha⟩ := exists_ne (x s.length)
  let y : ℕ → A :=
    fun i => if hi : i < s.length then s.get ⟨i, hi⟩ else if i = s.length then a else x i
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    simp [y, hi]
  · intro hxy
    have hyx := congrFun hxy s.length
    exact ha (by simpa [y] using hyx)

theorem sequence_space_perfect [TopologicalSpace A] [DiscreteTopology A] [Nontrivial A] :
    PerfectSpace (ℕ → A) := by
  refine ⟨?_⟩
  rw [preperfect_iff_nhds]
  intro x _ U hU
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV_open, hxV⟩
  obtain ⟨s, _hxs, hsV⟩ := exists_cyl_subset_of_mem_open (A := A) hxV hV_open
  obtain ⟨y, hys, hy_ne⟩ := exists_mem_cyl_ne s x
  exact ⟨y, ⟨hVU (hsV hys), mem_univ _⟩, hy_ne⟩

theorem isOpen_eq_iUnion_cyl [TopologicalSpace A] [DiscreteTopology A]
    {U : Set (ℕ → A)} (hU : IsOpen U) :
    U = ⋃ s : {s : finseq A // cyl s ⊆ U}, cyl s.1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open (A := A) hx hU
    exact Set.mem_iUnion.2 ⟨⟨s, hsU⟩, hxs⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hxs⟩
    exact s.2 hxs

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    Each cylinder is also closed: its complement is
    $$
    \SetDifference{A^\omega}{\cyl{s}}
    =
    \bigcup\{\cyl{t}:t\in\seqPower{A}{|s|},\ t\ne s\},
    $$
    which is open as a union of cylinders. Hence every cylinder is clopen, and both $\CantorSpace$ and $\BaireSpace$ are
    zero-dimensional.
-/
theorem compl_cyl_eq_iUnion_same_length_ne (s : finseq A) :
    (cyl s)ᶜ =
      ⋃ t : {t : finseq A // t.length = s.length ∧ t ≠ s}, cyl t.1 := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.2 ⟨⟨seqPrefix x s.length, by simp, ?_⟩, mem_cyl_seqPrefix x s.length⟩
    intro hseq
    exact hx (by simpa [hseq] using mem_cyl_seqPrefix x s.length)
  · intro hx hxs
    rcases Set.mem_iUnion.1 hx with ⟨t, hxt⟩
    apply t.2.2
    apply List.ext_get
    · exact t.2.1
    · intro i hi htlen
      have hslen : i < s.length := by simpa [t.2.1] using hi
      have hlen : i < t.1.length := hi
      calc
        t.1.get ⟨i, hlen⟩ = x i := (hxt i hlen).symm
        _ = s.get ⟨i, hslen⟩ := hxs i hslen

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The branching degree is the main difference. In Cantor space, the partition at level $n$ is finite:
    $$
    \CantorSpace=\InternalDisjointUnion_{t\in\seqPower{2}{n}}\cyl{t},
    \qquad
    |\seqPower{2}{n}|=2^n<\infty.
    $$
    By contrast, in Baire space the partition at level $n$ is countable:
    $$
    \BaireSpace=\InternalDisjointUnion_{t\in\seqPower{\omega}{n}}\cyl{t},
    \qquad
    \seqPower{\omega}{n}\text{ is countable}.
    $$
    Thus the same level-by-level prefix partition exists in both spaces, but the Baire-space partition is countably
    branching rather than finite and binary.
-/
theorem iUnion_cyl_level (n : ℕ) :
    (⋃ s : {s : finseq A // s.length = n}, cyl s.1) = (Set.univ : Set (ℕ → A)) := by
  ext x
  constructor
  · intro
    exact Set.mem_univ x
  · intro
    exact Set.mem_iUnion.2 ⟨⟨seqPrefix x n, by simp⟩, mem_cyl_seqPrefix x n⟩

noncomputable def levelEquiv (A : Type u) (n : ℕ) :
    {s : finseq A // s.length = n} ≃ (Fin n → A) where
  toFun s := fun i => s.1.get ⟨i, by rw [s.2]; exact i.2⟩
  invFun f := ⟨List.ofFn f, by simp⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply List.ext_get
    · simp [s.2]
    · intro i hi hslen
      simp
  right_inv := by
    intro f
    funext i
    simp

noncomputable instance levelFintype [Fintype A] (n : ℕ) :
    Fintype {s : finseq A // s.length = n} :=
  Fintype.ofEquiv (Fin n → A) (levelEquiv A n).symm

theorem level_card [Fintype A] (n : ℕ) :
    Fintype.card {s : finseq A // s.length = n} = Fintype.card A ^ n := by
  rw [Fintype.card_congr (levelEquiv A n)]
  exact Fintype.card_pi_const A n

theorem cantor_level_card (n : ℕ) :
    Fintype.card {s : finseq Bool // s.length = n} = 2 ^ n := by
  simpa [Fintype.card_bool] using level_card (A := Bool) n

theorem baire_level_countable (n : ℕ) :
    Countable {s : finseq ℕ // s.length = n} := by
  infer_instance

theorem cantor_cyl_clopen (s : finseq Bool) :
    IsClopen (cyl s : Set cantor_space) :=
  isClopen_cyl s

theorem baire_cyl_clopen (s : finseq ℕ) :
    IsClopen (cyl s : Set baire_space) :=
  isClopen_cyl s

end Cylinders

section SequenceMetric

variable {A : Type u} [DecidableEq A]

/-!
## Standard sequence metric

| Book notation | Lean name |
| --- | --- |
| first coordinate where two sequences differ | `firstDiffIndex x y` |
| agreement on the first `n` coordinates | `agreeOnPrefix n x y` |
| `\SeqMetric{x}{y}` | `seqMetric x y` |
-/

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    We use the \termdefine{standard sequence metric} on $A^\omega$:
    $$
    \SeqMetric{x}{y}:=
    \begin{cases}
    0, & x=y,\\
    2^{-\min\{i:x_i\ne y_i\}}, & x\ne y.
    \end{cases}
    $$
-/
/-- The first coordinate where two distinct infinite sequences differ.
For equal sequences this is defined to be `0`, so statements that use it
for mathematical content should usually carry the hypothesis `x ≠ y`. -/
noncomputable def firstDiffIndex (x y : ℕ → A) : ℕ :=
  by
    classical
    exact if h : x = y then 0 else Nat.find (Function.ne_iff.mp h)

/-- Two infinite sequences agree on the first `n` coordinates. -/
def agreeOnPrefix (n : ℕ) (x y : ℕ → A) : Prop :=
  ∀ i, i < n → x i = y i

/-- Book notation `\SeqMetric{x}{y}`:
the standard sequence distance, expressed using the first differing coordinate. -/
noncomputable def seqMetric (x y : ℕ → A) : ℝ :=
  by
    classical
    exact if h : x = y then 0 else ((1 / 2 : ℝ) ^ firstDiffIndex x y)

theorem firstDiffIndex_spec {x y : ℕ → A} (hxy : x ≠ y) :
    x (firstDiffIndex x y) ≠ y (firstDiffIndex x y) := by
  classical
  simpa [firstDiffIndex, hxy] using Nat.find_spec (Function.ne_iff.mp hxy)

theorem firstDiffIndex_min {x y : ℕ → A} (hxy : x ≠ y) {i : ℕ}
    (hi : i < firstDiffIndex x y) :
    x i = y i := by
  classical
  by_contra hne
  exact Nat.find_min (Function.ne_iff.mp hxy) (by simpa [firstDiffIndex, hxy] using hi) hne

theorem firstDiffIndex_le_of_ne_at {x y : ℕ → A} (h : x i ≠ y i) :
    firstDiffIndex x y ≤ i := by
  classical
  have hxy : x ≠ y := by
    intro hxy
    exact h (by rw [hxy])
  simpa [firstDiffIndex, hxy] using Nat.find_min' (Function.ne_iff.mp hxy) h

theorem firstDiffIndex_comm (x y : ℕ → A) :
    firstDiffIndex x y = firstDiffIndex y x := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [firstDiffIndex]
  · have hyx : y ≠ x := fun hyx => hxy hyx.symm
    have hfind :
        Nat.find (Function.ne_iff.mp hxy) = Nat.find (Function.ne_iff.mp hyx) := by
      exact Nat.find_congr' (by intro n; exact ne_comm)
    simp [firstDiffIndex, hxy, hyx, hfind]

theorem min_firstDiffIndex_le {x y z : ℕ → A} (hxz : x ≠ z) :
    min (firstDiffIndex x y) (firstDiffIndex y z) ≤ firstDiffIndex x z := by
  by_contra hnot
  have hlt : firstDiffIndex x z < min (firstDiffIndex x y) (firstDiffIndex y z) :=
    Nat.lt_of_not_ge hnot
  have hxy : firstDiffIndex x z < firstDiffIndex x y := lt_of_lt_of_le hlt (Nat.min_le_left _ _)
  have hyz : firstDiffIndex x z < firstDiffIndex y z := lt_of_lt_of_le hlt (Nat.min_le_right _ _)
  have hxyeq : x (firstDiffIndex x z) = y (firstDiffIndex x z) := by
    by_cases hxy' : x = y
    · subst y
      rfl
    · exact firstDiffIndex_min hxy' hxy
  have hyzeq : y (firstDiffIndex x z) = z (firstDiffIndex x z) := by
    by_cases hyz' : y = z
    · subst z
      rfl
    · exact firstDiffIndex_min hyz' hyz
  exact firstDiffIndex_spec hxz (hxyeq.trans hyzeq)

theorem agreeOnPrefix_of_le_firstDiffIndex {x y : ℕ → A} (hxy : x ≠ y) {n : ℕ}
    (hn : n ≤ firstDiffIndex x y) :
    agreeOnPrefix n x y := by
  intro i hi
  exact firstDiffIndex_min hxy (lt_of_lt_of_le hi hn)

@[simp]
theorem seqMetric_self (x : ℕ → A) :
    seqMetric x x = 0 := by
  classical
  simp [seqMetric]

theorem seqMetric_of_ne {x y : ℕ → A} (hxy : x ≠ y) :
    seqMetric x y = ((1 / 2 : ℝ) ^ firstDiffIndex x y) := by
  classical
  simp [seqMetric, hxy]

theorem seqMetric_pos_of_ne {x y : ℕ → A} (hxy : x ≠ y) :
    0 < seqMetric x y := by
  rw [seqMetric_of_ne hxy]
  positivity

theorem seqMetric_nonneg (x y : ℕ → A) :
    0 ≤ seqMetric x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [seqMetric_self]
  · exact (seqMetric_pos_of_ne hxy).le

theorem seqMetric_eq_zero_iff {x y : ℕ → A} :
    seqMetric x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    exact (seqMetric_pos_of_ne hxy).ne' h
  · intro h
    subst y
    simp [seqMetric_self]

theorem seqMetric_symm (x y : ℕ → A) :
    seqMetric x y = seqMetric y x := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [seqMetric_self]
  · have hyx : y ≠ x := fun hyx => hxy hyx.symm
    rw [seqMetric_of_ne hxy, seqMetric_of_ne hyx, firstDiffIndex_comm]

theorem seqMetric_le_one (x y : ℕ → A) :
    seqMetric x y ≤ 1 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [seqMetric_self]
  · rw [seqMetric_of_ne hxy]
    exact pow_le_one₀ (by norm_num) (by norm_num)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    Symmetry and definiteness are immediate from the definition. For the triangle inequality, it is
    enough to prove the stronger ultrametric inequality
    $$
    \SeqMetric{x}{y}\le
    \max\{\SeqMetric{x}{z},\SeqMetric{z}{y}\}.
    $$
    If $x=y$ this is trivial. Otherwise let $k$ be the least coordinate at which $x$ and $y$ differ. At coordinate $k$, the
    value $z_k$ differs from at least one of $x_k$ and $y_k$. Hence either $\SeqMetric{x}{z}\ge 2^{-k}$ or
    $\SeqMetric{z}{y}\ge 2^{-k}$, while $\SeqMetric{x}{y}=2^{-k}$.
    This proves the ultrametric inequality and therefore the triangle inequality.
-/
theorem seqMetric_ultrametric (x y z : ℕ → A) :
    seqMetric x z ≤ max (seqMetric x y) (seqMetric y z) := by
  classical
  by_cases hxz : x = z
  · subst z
    simp [seqMetric_self, seqMetric_nonneg]
  by_cases hxy : x = y
  · subst y
    simp [seqMetric_self]
  by_cases hyz : y = z
  · subst z
    simp [seqMetric_self]
  rw [seqMetric_of_ne hxz, seqMetric_of_ne hxy, seqMetric_of_ne hyz]
  have hmin := min_firstDiffIndex_le (A := A) (x := x) (y := y) (z := z) hxz
  have hpow :
      ((1 / 2 : ℝ) ^ firstDiffIndex x z) ≤
        ((1 / 2 : ℝ) ^ min (firstDiffIndex x y) (firstDiffIndex y z)) := by
    exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hmin
  have hmax :
      ((1 / 2 : ℝ) ^ min (firstDiffIndex x y) (firstDiffIndex y z)) =
        max ((1 / 2 : ℝ) ^ firstDiffIndex x y)
          ((1 / 2 : ℝ) ^ firstDiffIndex y z) := by
    by_cases hle : firstDiffIndex x y ≤ firstDiffIndex y z
    · rw [min_eq_left hle, max_eq_left]
      exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hle
    · have hle' : firstDiffIndex y z ≤ firstDiffIndex x y := le_of_not_ge hle
      rw [min_eq_right hle', max_eq_right]
      exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hle'
  exact hpow.trans_eq hmax

theorem seqMetric_triangle (x y z : ℕ → A) :
    seqMetric x z ≤ seqMetric x y + seqMetric y z := by
  exact (seqMetric_ultrametric x y z).trans
    (max_le_add_of_nonneg (seqMetric_nonneg _ _) (seqMetric_nonneg _ _))

theorem prefixOfSeq_iff_eq_or_length_le_firstDiffIndex {s : finseq A} {x y : ℕ → A}
    (hx : prefixOfSeq s x) :
    prefixOfSeq s y ↔ x = y ∨ s.length ≤ firstDiffIndex x y := by
  constructor
  · intro hy
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      by_contra hnot
      have hlt : firstDiffIndex x y < s.length := Nat.lt_of_not_ge hnot
      have hdiff := firstDiffIndex_spec hxy
      have hx_at := hx (firstDiffIndex x y) hlt
      have hy_at := hy (firstDiffIndex x y) hlt
      exact hdiff (hx_at.trans hy_at.symm)
  · intro h
    rcases h with rfl | hle
    · exact hx
    · intro i hi
      by_cases hxy : x = y
      · subst y
        exact hx i hi
      · exact (agreeOnPrefix_of_le_firstDiffIndex hxy hle i hi).symm.trans (hx i hi)

theorem mem_cyl_iff_eq_or_length_le_firstDiffIndex {s : finseq A} {x y : ℕ → A}
    (hx : x ∈ cyl s) :
    y ∈ cyl s ↔ x = y ∨ s.length ≤ firstDiffIndex x y :=
  prefixOfSeq_iff_eq_or_length_le_firstDiffIndex hx

/-- Radius used in the book's cylinder-ball comparison. For length `0`, this is `2`;
for positive length `k`, this is `(1 / 2)^(k - 1)`. -/
noncomputable def cylinderBallRadius (k : ℕ) : ℝ :=
  if k = 0 then 2 else (1 / 2 : ℝ) ^ (k - 1)

theorem cylinderBallRadius_pos (k : ℕ) :
    0 < cylinderBallRadius k := by
  unfold cylinderBallRadius
  split
  · norm_num
  · positivity

theorem seqMetric_lt_cylinderBallRadius_iff {s : finseq A} {x y : ℕ → A}
    (hx : x ∈ cyl s) :
    seqMetric x y < cylinderBallRadius s.length ↔ y ∈ cyl s := by
  classical
  by_cases hlen : s.length = 0
  · have hs : s = [] := List.length_eq_zero_iff.mp hlen
    subst s
    constructor
    · intro _
      simp
    · intro _
      have hle := seqMetric_le_one x y
      simp [cylinderBallRadius]
      linarith
  · constructor
    · intro hdist
      rw [mem_cyl_iff_eq_or_length_le_firstDiffIndex hx]
      by_cases hxy : x = y
      · exact Or.inl hxy
      · right
        by_contra hnot
        have hlt : firstDiffIndex x y < s.length := Nat.lt_of_not_ge hnot
        have hlepred : firstDiffIndex x y ≤ s.length - 1 := Nat.le_sub_one_of_lt hlt
        have hge :
            cylinderBallRadius s.length ≤ seqMetric x y := by
          rw [seqMetric_of_ne hxy, cylinderBallRadius, ite_eq_right hlen]
          exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
            (by norm_num : (1 / 2 : ℝ) ≤ 1) hlepred
        exact not_lt_of_ge hge hdist
    · intro hy
      rw [mem_cyl_iff_eq_or_length_le_firstDiffIndex hx] at hy
      rcases hy with rfl | hle
      · rw [seqMetric_self]
        exact cylinderBallRadius_pos s.length
      · rw [cylinderBallRadius, ite_eq_right hlen]
        by_cases hxy : x = y
        · subst y
          rw [seqMetric_self]
          positivity
        · rw [seqMetric_of_ne hxy]
          have hlt : s.length - 1 < firstDiffIndex x y := by
            exact Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero hlen) hle
          exact pow_lt_pow_right_of_lt_one₀ (by norm_num : 0 < (1 / 2 : ℝ))
            (by norm_num : (1 / 2 : ℝ) < 1) hlt

theorem cyl_eq_seqMetric_ball {s : finseq A} {x : ℕ → A} (hx : x ∈ cyl s) :
    cyl s = {y : ℕ → A | seqMetric x y < cylinderBallRadius s.length} := by
  ext y
  exact (seqMetric_lt_cylinderBallRadius_iff hx).symm

/-- Type synonym for a sequence space equipped with the standard prefix metric. -/
def sequence_metric_space (A : Type u) : Type u :=
  ℕ → A

/-- Cantor space equipped with the standard prefix metric. -/
abbrev cantor_metric_space : Type :=
  sequence_metric_space Bool

/-- Baire space equipped with the standard prefix metric. -/
abbrev baire_metric_space : Type :=
  sequence_metric_space ℕ

namespace sequence_metric_space

noncomputable instance [TopologicalSpace A] [DiscreteTopology A] :
    MetricSpace (sequence_metric_space A) :=
  PiNat.metricSpace

end sequence_metric_space

theorem firstDiffIndex_eq_pinat_firstDiff (x y : ℕ → A) :
    firstDiffIndex x y = PiNat.firstDiff x y := by
  by_cases hxy : x = y
  · subst y
    simp [firstDiffIndex, PiNat.firstDiff_def]
  · apply le_antisymm
    · exact firstDiffIndex_le_of_ne_at (PiNat.apply_firstDiff_ne hxy)
    · by_contra hnot
      have hlt : firstDiffIndex x y < PiNat.firstDiff x y := Nat.lt_of_not_ge hnot
      exact firstDiffIndex_spec hxy (PiNat.apply_eq_of_lt_firstDiff hlt)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\SeqMetricName$ is a metric on both $\CantorSpace$ and $\BaireSpace$, and in each case $\SeqMetricName$ is compatible with the
-/
theorem seqMetric_eq_sequenceMetricSpace_dist [TopologicalSpace A] [DiscreteTopology A]
    (x y : sequence_metric_space A) :
    seqMetric x y = dist x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [seqMetric_self]
  · have hxy' : (x : ℕ → A) ≠ y := hxy
    rw [seqMetric_of_ne hxy']
    change (1 / 2 : ℝ) ^ firstDiffIndex x y = @dist (ℕ → A) PiNat.dist x y
    rw [PiNat.dist_eq_of_ne hxy']
    rw [firstDiffIndex_eq_pinat_firstDiff]

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\SeqMetricName$ is a metric on both $\CantorSpace$ and $\BaireSpace$, and in each case $\SeqMetricName$ is compatible with the
-/
theorem cyl_eq_metric_ball [TopologicalSpace A] [DiscreteTopology A]
    {s : finseq A} {x : sequence_metric_space A} (hx : (x : ℕ → A) ∈ cyl s) :
    (cyl s : Set (sequence_metric_space A)) = Metric.ball x (cylinderBallRadius s.length) := by
  rw [cyl_eq_seqMetric_ball hx]
  ext y
  simp only [Set.mem_ofPred_eq, Metric.ball]
  rw [seqMetric_eq_sequenceMetricSpace_dist]
  rw [dist_comm]
  rfl

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    It remains to compare the metric balls with cylinders. Fix $x\in\cyl{s}$ and put $k=|s|$. A point $y$ belongs to
    $\cyl{s}$ exactly when $x$ and $y$ agree on the first $k$ coordinates. If $k=0$, this says only that
    $\cyl{\emptySeq}=A^\omega$. If $k>0$, agreement on the first $k$ coordinates is equivalent to
    $\SeqMetric{x}{y}<2^{-(k-1)}$: any disagreement before coordinate $k$ has distance at least $2^{-(k-1)}$, while
    agreement through coordinate $k-1$ gives distance at most $2^{-k}$ unless $x=y$. Hence, for nonempty $s$,
    $\cyl{s}=\MetricBall{\SeqMetricName}{x}{2^{-(|s|-1)}}$.
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\SeqMetricName$ is a metric on both $\CantorSpace$ and $\BaireSpace$, and in each case $\SeqMetricName$ is compatible with the
-/
theorem cyl_eq_metric_ball_nonempty [TopologicalSpace A] [DiscreteTopology A]
    {s : finseq A} (hs : s ≠ []) {x : sequence_metric_space A}
    (hx : (x : ℕ → A) ∈ cyl s) :
    (cyl s : Set (sequence_metric_space A)) = Metric.ball x ((1 / 2 : ℝ) ^ (s.length - 1)) := by
  rw [cyl_eq_metric_ball hx]
  have hlen : s.length ≠ 0 := by
    intro hzero
    exact hs (List.length_eq_zero_iff.mp hzero)
  simp [cylinderBallRadius, hlen]

theorem mem_metric_ball_cylinderBallRadius_iff [TopologicalSpace A] [DiscreteTopology A]
    {s : finseq A} {x y : sequence_metric_space A} (hx : (x : ℕ → A) ∈ cyl s) :
    y ∈ Metric.ball x (cylinderBallRadius s.length) ↔ (y : ℕ → A) ∈ cyl s := by
  rw [← cyl_eq_metric_ball hx]

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    Conversely, given a metric ball $\MetricBall{\SeqMetricName}{x}{\varepsilon}$ around $x$, choose $n$ with
    $2^{-n}<\varepsilon$. The nonempty-prefix equality gives
    $$
    \cyl{\restrict{x}{n+1}}
    =\MetricBall{\SeqMetricName}{x}{2^{-n}}
    \IncludedIn\MetricBall{\SeqMetricName}{x}{\varepsilon}.
    $$
    Since the cylinders already form the standard base for the product topology, the metric topology and the product
    topology coincide.
-/
theorem exists_cyl_subset_seqMetric_ball {x : ℕ → A} {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, cyl (seqPrefix x (n + 1)) ⊆ {y : ℕ → A | seqMetric x y < ε} := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, fun y hy => ?_⟩
  have hball :=
    (seqMetric_lt_cylinderBallRadius_iff (A := A) (x := x) (s := seqPrefix x (n + 1))
      (mem_cyl_seqPrefix x (n + 1))).2 hy
  have hball' : seqMetric x y < cylinderBallRadius (n + 1) := by
    simpa using hball
  have hradius : cylinderBallRadius (n + 1) = (1 / 2 : ℝ) ^ n := by
    simp [cylinderBallRadius]
  rw [hradius] at hball'
  exact hball'.trans hn

theorem exists_cyl_subset_metric_ball [TopologicalSpace A] [DiscreteTopology A]
    {x : sequence_metric_space A} {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (cyl (seqPrefix (x : ℕ → A) (n + 1)) : Set (sequence_metric_space A)) ⊆
      Metric.ball (α := sequence_metric_space A) x ε := by
  obtain ⟨n, hn⟩ := exists_cyl_subset_seqMetric_ball (A := A) (x := (x : ℕ → A)) hε
  refine ⟨n, ?_⟩
  intro y hy
  have hseq : seqMetric (x : ℕ → A) (y : ℕ → A) < ε := hn hy
  have hdist : dist x y < ε := by
    rw [← seqMetric_eq_sequenceMetricSpace_dist]
    exact hseq
  exact (Metric.mem_ball' (x := x) (y := y) (ε := ε)).2 hdist

end SequenceMetric

section CylinderCodesPrefixTrees

variable {A : Type u}

/-!
## Cylinder codes and prefix trees

| Book notation | Lean name |
| --- | --- |
| up-set in the prefix order | `IsPrefixUpSet B` |
| saturated up-set | `IsSaturatedPrefixUpSet B` |
| `\CylinderCode{B}` | `cylinderCode B` |
| `\OpenCylinderCode{U}` | `openCylinderCode U` |
| subtree | `IsSubtree T` |
| pruned subtree | `IsPruned T` |
| `\TreeBody{T}` | `treeBody T` |
| `\ClosedTreeCode{F}` | `closedTreeCode F` |
-/

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    An \termdefine{up-set} is a set $B\IncludedIn\finseq{A}$ such that $s\in B$ and $s\prefixOf t$ imply $t\in B$.
    An up-set $B$ is \termdefine{saturated} when every prefix whose branches all eventually reach $B$ already lies in $B$:
    if for every $x\in\cyl{s}\IncludedIn A^\omega$ there is some $n\in\omega$ with $\restrict{x}{n}\in B$, then $s\in B$.
-/
/-- Up-set for the finite-prefix order. -/
def IsPrefixUpSet (B : Set (finseq A)) : Prop :=
  ∀ ⦃s t : finseq A⦄, s ∈ B → prefixOf s t → t ∈ B

/-- Saturation condition for a prefix up-set. -/
def IsSaturatedPrefixUpSet (B : Set (finseq A)) : Prop :=
  IsPrefixUpSet B ∧
    ∀ s : finseq A, (∀ x : ℕ → A, x ∈ cyl s → ∃ n : ℕ, seqPrefix x n ∈ B) → s ∈ B

/-- Book notation `\CylinderCode{B}`:
an up-set of finite prefixes codes the union of its cylinders. -/
def cylinderCode (B : Set (finseq A)) : Set (ℕ → A) :=
  ⋃ s : {s : finseq A // s ∈ B}, cyl s.1

/-- Book notation `\OpenCylinderCode{U}`:
an open set is coded by the cylinders contained in it. -/
def openCylinderCode (U : Set (ℕ → A)) : Set (finseq A) :=
  {s | cyl s ⊆ U}

theorem mem_cylinderCode {B : Set (finseq A)} {x : ℕ → A} :
    x ∈ cylinderCode B ↔ ∃ s : finseq A, s ∈ B ∧ x ∈ cyl s := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hxs⟩
    exact ⟨s.1, s.2, hxs⟩
  · rintro ⟨s, hsB, hxs⟩
    exact Set.mem_iUnion.2 ⟨⟨s, hsB⟩, hxs⟩

theorem isOpen_cylinderCode [TopologicalSpace A] [DiscreteTopology A] (B : Set (finseq A)) :
    IsOpen (cylinderCode B) := by
  rw [cylinderCode]
  exact isOpen_iUnion fun s => isOpen_cyl s.1

theorem openCylinderCode_isPrefixUpSet (U : Set (ℕ → A)) :
    IsPrefixUpSet (openCylinderCode U) := by
  intro s t hsU hst
  exact (cyl_subset_of_prefix hst).trans hsU

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] If $B$ is an up-set, then $\CylinderCode{B}$ is open.
    If $U$ is open, then $\OpenCylinderCode{U}$ is an up-set because $\cyl{t}\IncludedIn\cyl{s}$ whenever $s\prefixOf t$.
    If $\CylinderCode{B}\IncludedIn U$ and $s\in B$, then $\cyl{s}\IncludedIn\CylinderCode{B}\IncludedIn U$, so
    $s\in\OpenCylinderCode{U}$.
    Conversely, if $B\IncludedIn\OpenCylinderCode{U}$, then every cylinder $\cyl{s}$ with $s\in B$ is contained in $U$,
    hence $\CylinderCode{B}\IncludedIn U$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    The assignments $$ \begin{aligned} \CylinderCode{\cdot}:\PrefixUpSets{\omega}&\to\OpenSets{\BaireSpace}, & \CylinderCode{B}&:=\bigcup_{s\in B}\cyl{s},\\ \OpenCylinderCode{\cdot}:\OpenSets{\BaireSpace}&\to\PrefixUpSets{\omega}, & \OpenCylinderCode{U}&:=\{s\in\finseq{\omega}:\cyl{s}\IncludedIn U\} \end{aligned} $$ form a Galois connection:
-/
theorem cylinderCode_subset_iff_subset_openCylinderCode
    {B : Set (finseq A)} {U : Set (ℕ → A)} :
    cylinderCode B ⊆ U ↔ B ⊆ openCylinderCode U := by
  constructor
  · intro h s hsB x hxs
    exact h (mem_cylinderCode.2 ⟨s, hsB, hxs⟩)
  · intro h x hx
    rcases mem_cylinderCode.1 hx with ⟨s, hsB, hxs⟩
    exact h hsB hxs

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    Open sets in $\BaireSpace$ are in one-to-one correspondence with saturated up-sets of $\finseq{\omega}$. The correspondence sends an open
-/
theorem open_eq_cylinderCode_openCylinderCode [TopologicalSpace A] [DiscreteTopology A]
    {U : Set (ℕ → A)} (hU : IsOpen U) :
    cylinderCode (openCylinderCode U) = U := by
  ext x
  constructor
  · intro hx
    rcases mem_cylinderCode.1 hx with ⟨s, hsU, hxs⟩
    exact hsU hxs
  · intro hx
    obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open (A := A) hx hU
    exact mem_cylinderCode.2 ⟨s, hsU, hxs⟩

theorem openCylinderCode_isSaturated [TopologicalSpace A] [DiscreteTopology A]
    {U : Set (ℕ → A)} (_hU : IsOpen U) :
    IsSaturatedPrefixUpSet (openCylinderCode U) := by
  refine ⟨openCylinderCode_isPrefixUpSet U, ?_⟩
  intro s hbranches x hxs
  rcases hbranches x hxs with ⟨n, hn⟩
  exact hn (mem_cyl_seqPrefix x n)

theorem subset_openCylinderCode_cylinderCode (B : Set (finseq A)) :
    B ⊆ openCylinderCode (cylinderCode B) := by
  intro s hsB x hxs
  exact mem_cylinderCode.2 ⟨s, hsB, hxs⟩

theorem openCylinderCode_cylinderCode_subset_of_saturated
    {B : Set (finseq A)} (hB : IsSaturatedPrefixUpSet B) :
    openCylinderCode (cylinderCode B) ⊆ B := by
  intro s hs
  exact hB.2 s fun x hxs => by
    have hxcode : x ∈ cylinderCode B := hs hxs
    rcases mem_cylinderCode.1 hxcode with ⟨t, htB, hxt⟩
    refine ⟨t.length, ?_⟩
    have hprefix : prefixOf t (seqPrefix x t.length) := by
      rw [seqPrefix_eq_of_mem_cyl hxt]
    exact hB.1 htB hprefix

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    Open sets in $\BaireSpace$ are in one-to-one correspondence with saturated up-sets of $\finseq{\omega}$. The correspondence sends an open
-/
theorem openCylinderCode_cylinderCode_eq_of_saturated
    {B : Set (finseq A)} (hB : IsSaturatedPrefixUpSet B) :
    openCylinderCode (cylinderCode B) = B := by
  exact Set.Subset.antisymm (openCylinderCode_cylinderCode_subset_of_saturated hB)
    (subset_openCylinderCode_cylinderCode B)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] If $U$ is open, then every $x\in U$ lies in some cylinder $\cyl{s}\IncludedIn U$.
    Thus $U=\CylinderCode{\OpenCylinderCode{U}}$.
    The up-set $\OpenCylinderCode{U}$ is saturated: if every branch through $s$ eventually reaches
    $\OpenCylinderCode{U}$, then every point of $\cyl{s}$ lies in $U$, so $\cyl{s}\IncludedIn U$ and hence
    $s\in\OpenCylinderCode{U}$.
    If $B$ is saturated, then applying $\OpenCylinderCode{\cdot}$ to $\CylinderCode{B}$ returns $B$.
    Indeed, $B\IncludedIn\OpenCylinderCode{\CylinderCode{B}}$ is immediate.
    Conversely, if $s\in\OpenCylinderCode{\CylinderCode{B}}$, then every $x\in\cyl{s}$ has some prefix in $B$.
    Saturation of $B$ therefore gives $s\in B$.
    This proves that the two assignments are inverse.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    Open sets in $\BaireSpace$ are in one-to-one correspondence with saturated up-sets of $\finseq{\omega}$. The correspondence sends an open
-/
theorem saturated_upSet_open_correspondence [TopologicalSpace A] [DiscreteTopology A]
    (U : Set (ℕ → A)) :
    IsOpen U ↔ ∃ B : Set (finseq A),
      IsSaturatedPrefixUpSet B ∧ U = cylinderCode B := by
  constructor
  · intro hU
    exact ⟨openCylinderCode U, openCylinderCode_isSaturated hU,
      (open_eq_cylinderCode_openCylinderCode hU).symm⟩
  · rintro ⟨B, _, rfl⟩
    exact isOpen_cylinderCode B

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    A \termdefine{subtree} is a set $T\IncludedIn\finseq{\omega}$ downward closed under initial segments:
    if $t\in T$ and $s\prefixOf t$, then $s\in T$.
    Write $\PrefixSubtrees{\omega}$ for the poset of subtrees of the full prefix tree, ordered by inclusion.
-/
/-- Downward-closed subtree of the full prefix tree. -/
def IsSubtree (T : Set (finseq A)) : Prop :=
  ∀ ⦃s t : finseq A⦄, t ∈ T → prefixOf s t → s ∈ T

/-- Body of a prefix tree: the infinite branches whose finite prefixes all lie in `T`. -/
def treeBody (T : Set (finseq A)) : Set (ℕ → A) :=
  {x | ∀ n : ℕ, seqPrefix x n ∈ T}

/-- Book notation `\ClosedTreeCode{F}`:
finite prefixes whose cylinders meet the closed set code target `F`. -/
def closedTreeCode (F : Set (ℕ → A)) : Set (finseq A) :=
  {s | (cyl s ∩ F).Nonempty}

/-- Pruned subtree: every node lies on an infinite branch through the tree. -/
def IsPruned (T : Set (finseq A)) : Prop :=
  ∀ ⦃s : finseq A⦄, s ∈ T → ∃ x : ℕ → A, x ∈ treeBody T ∧ x ∈ cyl s

theorem mem_treeBody {T : Set (finseq A)} {x : ℕ → A} :
    x ∈ treeBody T ↔ ∀ n : ℕ, seqPrefix x n ∈ T :=
  Iff.rfl

theorem treeBody_univ :
    treeBody (Set.univ : Set (finseq A)) = (Set.univ : Set (ℕ → A)) := by
  ext x
  simp [treeBody]

theorem univ_isSubtree :
    IsSubtree (Set.univ : Set (finseq A)) := by
  intro s t ht hst
  exact mem_univ s

theorem univ_isPruned [Inhabited A] :
    IsPruned (Set.univ : Set (finseq A)) := by
  intro s hs
  exact ⟨extendFinseq s, by simp [treeBody], extendFinseq_mem_cyl s⟩

noncomputable def treeBodyUnivHomeomorph [TopologicalSpace A] :
    treeBody (Set.univ : Set (finseq A)) ≃ₜ (ℕ → A) :=
  (Homeomorph.setCongr (treeBody_univ (A := A))).trans (Homeomorph.Set.univ (ℕ → A))

/-- Prefix tree whose allowed successors at `s` are exactly `i < k s`. -/
def boundedBranchingTree (k : finseq ℕ → ℕ) : Set (finseq ℕ) :=
  {s | ∀ n (hn : n < s.length), s.get ⟨n, hn⟩ < k (s.take n)}

@[simp]
theorem mem_boundedBranchingTree_nil (k : finseq ℕ → ℕ) :
    ([] : finseq ℕ) ∈ boundedBranchingTree k := by
  intro n hn
  cases hn

theorem boundedBranchingTree_isSubtree (k : finseq ℕ → ℕ) :
    IsSubtree (boundedBranchingTree k) := by
  intro s t ht hst n hn
  have hnt : n < t.length := lt_of_lt_of_le hn hst.length_le
  have htake : s.take n = t.take n := by
    have hs_eq : s = t.take s.length := List.prefix_iff_eq_take.mp hst
    rw [hs_eq, List.take_take]
    simp [Nat.min_eq_left (Nat.le_of_lt hn)]
  calc
    s.get ⟨n, hn⟩ = t.get ⟨n, hnt⟩ := by
      exact hst.getElem hn
    _ < k (t.take n) := ht n hnt
    _ = k (s.take n) := by rw [htake]

theorem boundedBranchingTree_child_mem_iff (k : finseq ℕ → ℕ) (s : finseq ℕ) (i : ℕ) :
    concat s [i] ∈ boundedBranchingTree k ↔
      s ∈ boundedBranchingTree k ∧ i < k s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n hn
      have hn_child : n < (concat s [i]).length := by
        simpa [concat] using lt_of_lt_of_le hn (Nat.le_succ s.length)
      have htake : (concat s [i]).take n = s.take n := by
        simpa [concat] using List.take_append_of_le_length (l₂ := [i]) (Nat.le_of_lt hn)
      simpa [concat, hn, htake] using h n hn_child
    · have hlast : s.length < (concat s [i]).length := by simp [concat]
      simpa [concat] using h s.length hlast
  · rintro ⟨hs, hi⟩ n hn
    by_cases hn_s : n < s.length
    · have htake : (concat s [i]).take n = s.take n := by
        simpa [concat] using List.take_append_of_le_length (l₂ := [i]) (Nat.le_of_lt hn_s)
      simpa [concat, hn_s, htake] using hs n hn_s
    · have hn_eq : n = s.length := by
        have hn_le : n ≤ s.length := by
          have hn_len : n < s.length + 1 := by
            simpa [concat] using hn
          exact Nat.lt_succ_iff.mp hn_len
        exact le_antisymm hn_le (not_lt.mp hn_s)
      subst n
      simpa [concat] using hi

theorem boundedBranchingTree_child_mem {k : finseq ℕ → ℕ} {s : finseq ℕ} {i : ℕ}
    (hs : s ∈ boundedBranchingTree k) (hi : i < k s) :
    concat s [i] ∈ boundedBranchingTree k :=
  (boundedBranchingTree_child_mem_iff k s i).2 ⟨hs, hi⟩

theorem boundedBranchingTree_lt_of_child_mem {k : finseq ℕ → ℕ} {s : finseq ℕ} {i : ℕ}
    (hsi : concat s [i] ∈ boundedBranchingTree k) :
    i < k s :=
  ((boundedBranchingTree_child_mem_iff k s i).1 hsi).2

theorem boundedBranchingTree_child_mem_iff_of_mem {k : finseq ℕ → ℕ}
    {s : finseq ℕ} (hs : s ∈ boundedBranchingTree k) (i : ℕ) :
    concat s [i] ∈ boundedBranchingTree k ↔ i < k s := by
  rw [boundedBranchingTree_child_mem_iff]
  exact and_iff_right hs

theorem boundedBranchingTree_has_two_children {k : finseq ℕ → ℕ}
    {s : finseq ℕ} (hs : s ∈ boundedBranchingTree k) (hk : 2 ≤ k s) :
    concat s [0] ∈ boundedBranchingTree k ∧
      concat s [1] ∈ boundedBranchingTree k ∧
        concat s [0] ≠ concat s [1] := by
  refine ⟨boundedBranchingTree_child_mem hs (by omega), ?_, ?_⟩
  · exact boundedBranchingTree_child_mem hs (by omega)
  · simp [concat]

theorem boundedBranchingTree_zero_extension_mem_treeBody {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s)
    {s : finseq ℕ} (hs : s ∈ boundedBranchingTree k) :
    extendFinseq s ∈ treeBody (boundedBranchingTree k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro j hj
      have hjn : j < n := by simpa [seqPrefix_length] using hj
      by_cases hjs : j < s.length
      · have htake_j :
            (seqPrefix (extendFinseq s) n).take j = s.take j := by
          rw [seqPrefix_take_of_le (extendFinseq s) (Nat.le_of_lt hjn)]
          rw [seqPrefix_extendFinseq_of_le s (Nat.le_of_lt hjs)]
        have hget :
            (seqPrefix (extendFinseq s) n).get ⟨j, hj⟩ = s.get ⟨j, hjs⟩ := by
          simp [seqPrefix, extendFinseq, hjs]
        calc
          (seqPrefix (extendFinseq s) n).get ⟨j, hj⟩ = s.get ⟨j, hjs⟩ := hget
          _ < k (s.take j) := hs j hjs
          _ = k ((seqPrefix (extendFinseq s) n).take j) := by rw [htake_j]
      · have hprefix_mem :
            (seqPrefix (extendFinseq s) n).take j ∈ boundedBranchingTree k := by
          rw [seqPrefix_take_of_le (extendFinseq s) (Nat.le_of_lt hjn)]
          exact ih j hjn
        have hget :
            (seqPrefix (extendFinseq s) n).get ⟨j, hj⟩ = 0 := by
          simp [seqPrefix, extendFinseq, hjs]
        calc
          (seqPrefix (extendFinseq s) n).get ⟨j, hj⟩ = 0 := hget
          _ < k ((seqPrefix (extendFinseq s) n).take j) :=
            lt_of_lt_of_le (by omega : 0 < 2) (hk hprefix_mem)

theorem boundedBranchingTree_isPruned_of_two_le {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) :
    IsPruned (boundedBranchingTree k) := by
  intro s hs
  exact ⟨extendFinseq s, boundedBranchingTree_zero_extension_mem_treeBody hk hs,
    extendFinseq_mem_cyl s⟩

theorem boundedBranchingTree_exists_branch_mem_cyl_ne {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s)
    {x : ℕ → ℕ} (hx : x ∈ treeBody (boundedBranchingTree k)) (n : ℕ) :
    ∃ y : ℕ → ℕ, y ∈ treeBody (boundedBranchingTree k) ∧
      y ∈ cyl (seqPrefix x n) ∧ y ≠ x := by
  let p : finseq ℕ := seqPrefix x n
  have hp : p ∈ boundedBranchingTree k := hx n
  let a : ℕ := if x n = 0 then 1 else 0
  have ha_lt : a < k p := by
    have hkp : 2 ≤ k p := hk hp
    by_cases hx0 : x n = 0
    · simp [a, hx0]
      omega
    · simp [a, hx0]
      omega
  have ha_ne : a ≠ x n := by
    by_cases hx0 : x n = 0
    · simp [a, hx0]
    · rw [show a = 0 by simp [a, hx0]]
      exact fun h => hx0 h.symm
  let c : finseq ℕ := concat p [a]
  have hc : c ∈ boundedBranchingTree k := boundedBranchingTree_child_mem hp ha_lt
  let y : ℕ → ℕ := extendFinseq c
  refine ⟨y, boundedBranchingTree_zero_extension_mem_treeBody hk hc, ?_, ?_⟩
  · exact cyl_concat_subset p [a] (by simpa [y, c] using extendFinseq_mem_cyl c)
  · intro hyx
    have hycoord := congrFun hyx n
    have hyn : y n = a := by
      simp [y, c, p, concat, extendFinseq, seqPrefix_length]
    exact ha_ne (hyn.symm.trans hycoord)

theorem boundedBranchingTree_treeBody_perfect {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) :
    PerfectSpace (treeBody (boundedBranchingTree k)) := by
  refine ⟨?_⟩
  rw [preperfect_iff_nhds]
  intro x _ U hU
  rcases (mem_nhds_subtype (treeBody (boundedBranchingTree k)) x U).mp hU with
    ⟨V, hV, hVU⟩
  rcases mem_nhds_iff.mp hV with ⟨O, hOV, hO_open, hxO⟩
  obtain ⟨s, hxs, hsO⟩ := exists_cyl_subset_of_mem_open (A := ℕ) hxO hO_open
  rcases boundedBranchingTree_exists_branch_mem_cyl_ne hk x.2 s.length with
    ⟨y, hybody, hycyl, hy_ne⟩
  have hys : y ∈ cyl s := by
    simpa [seqPrefix_eq_of_mem_cyl hxs] using hycyl
  refine ⟨⟨y, hybody⟩, ⟨hVU (hOV (hsO hys)), mem_univ _⟩, ?_⟩
  intro hyx
  exact hy_ne (congrArg Subtype.val hyx)

/-- A canonical prefix-code partition of binary space into `m` nonempty cylinders.
For `i + 1 < m`, the code is `1^i 0`; the last code is `1^i`. -/
def binaryChildCode (m i : ℕ) : finseq Bool :=
  if i + 1 < m then List.replicate i true ++ [false] else List.replicate i true

theorem mem_cyl_binaryChildCode_iff {m i : ℕ} (_hi : i < m) {x : ℕ → Bool} :
    x ∈ cyl (binaryChildCode m i) ↔
      (∀ r : ℕ, r < i → x r = true) ∧ (i + 1 < m → x i = false) := by
  by_cases hlast : i + 1 < m
  · constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro r hri
        have hrlen : r < (binaryChildCode m i).length := by
          simp [binaryChildCode, hlast]
          omega
        simpa [binaryChildCode, hlast, hri] using hx r hrlen
      · intro _hi_last
        have hilen : i < (binaryChildCode m i).length := by
          simp [binaryChildCode, hlast]
        simpa [binaryChildCode, hlast] using hx i hilen
    · rintro ⟨htrue, hfalse⟩ r hr
      by_cases hri : r < i
      · simpa [binaryChildCode, hlast, hri] using htrue r hri
      · have hr_len : r < i + 1 := by
          simpa [binaryChildCode, hlast] using hr
        have hri_eq : r = i := by omega
        subst r
        simpa [binaryChildCode, hlast] using hfalse hlast
  · constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro r hri
        have hrlen : r < (binaryChildCode m i).length := by
          simpa [binaryChildCode, hlast] using hri
        simpa [binaryChildCode, hlast] using hx r hrlen
      · intro hcontr
        exact False.elim (hlast hcontr)
    · rintro ⟨htrue, _hfalse⟩ r hr
      have hri : r < i := by
        simpa [binaryChildCode, hlast] using hr
      simpa [binaryChildCode, hlast] using htrue r hri

theorem binaryChildCode_length_pos {m i : ℕ} (hm : 2 ≤ m) (hi : i < m) :
    0 < (binaryChildCode m i).length := by
  by_cases hlast : i + 1 < m
  · simp [binaryChildCode, hlast]
  · have hi_last : i + 1 = m := by omega
    have hi_pos : 0 < i := by omega
    simpa [binaryChildCode, hlast] using hi_pos

theorem exists_mem_cyl_binaryChildCode (m : ℕ) (hm : 2 ≤ m) (x : ℕ → Bool) :
    ∃ i : {i : ℕ // i < m}, x ∈ cyl (binaryChildCode m i.1) := by
  classical
  by_cases hfalse : ∃ r : ℕ, r < m - 1 ∧ x r = false
  · let i : ℕ := Nat.find hfalse
    have hi_spec : i < m - 1 ∧ x i = false := Nat.find_spec hfalse
    have hi : i < m := by omega
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [mem_cyl_binaryChildCode_iff hi]
    refine ⟨?_, ?_⟩
    · intro r hri
      by_contra htrue
      have hxfalse : x r = false := by
        cases hxr : x r
        · rfl
        · exact False.elim (htrue hxr)
      exact (Nat.find_min hfalse hri) ⟨by omega, hxfalse⟩
    · intro _hi_last
      exact hi_spec.2
  · let i : ℕ := m - 1
    have hi : i < m := by omega
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [mem_cyl_binaryChildCode_iff hi]
    refine ⟨?_, ?_⟩
    · intro r hri
      by_contra htrue
      have hxfalse : x r = false := by
        cases hxr : x r
        · rfl
        · exact False.elim (htrue hxr)
      exact hfalse ⟨r, by simpa [i] using hri, hxfalse⟩
    · intro hi_last
      omega

theorem cyl_binaryChildCode_disjoint {m i j : ℕ} (_hm : 2 ≤ m)
    (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    Disjoint (cyl (binaryChildCode m i)) (cyl (binaryChildCode m j)) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxi' := (mem_cyl_binaryChildCode_iff hi).1 hxi
  have hxj' := (mem_cyl_binaryChildCode_iff hj).1 hxj
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · have hxi_last : i + 1 < m := by omega
    have hx_i_false : x i = false := hxi'.2 hxi_last
    have hx_i_true : x i = true := hxj'.1 i hij_lt
    simp [hx_i_true] at hx_i_false
  · have hxj_last : j + 1 < m := by omega
    have hx_j_false : x j = false := hxj'.2 hxj_last
    have hx_j_true : x j = true := hxi'.1 j hji_lt
    simp [hx_j_true] at hx_j_false

/-- Binary code accumulated from a current tree prefix `p` along a finite tail. -/
def boundedBranchingBinaryCodeFrom (k : finseq ℕ → ℕ) (p : finseq ℕ) :
    finseq ℕ → finseq Bool
  | [] => []
  | i :: s => binaryChildCode (k p) i ++
      boundedBranchingBinaryCodeFrom k (concat p [i]) s

/-- Binary code of a node in a bounded-branching tree. -/
def boundedBranchingBinaryCode (k : finseq ℕ → ℕ) (s : finseq ℕ) : finseq Bool :=
  boundedBranchingBinaryCodeFrom k [] s

theorem boundedBranchingBinaryCodeFrom_append_singleton
    (k : finseq ℕ → ℕ) (p s : finseq ℕ) (i : ℕ) :
    boundedBranchingBinaryCodeFrom k p (concat s [i]) =
      concat (boundedBranchingBinaryCodeFrom k p s)
        (binaryChildCode (k (concat p s)) i) := by
  induction s generalizing p with
  | nil =>
      simp [boundedBranchingBinaryCodeFrom, concat]
  | cons a t ih =>
      simp [boundedBranchingBinaryCodeFrom, concat, ih, List.append_assoc]

theorem boundedBranchingBinaryCode_concat (k : finseq ℕ → ℕ)
    (s : finseq ℕ) (i : ℕ) :
    boundedBranchingBinaryCode k (concat s [i]) =
      concat (boundedBranchingBinaryCode k s) (binaryChildCode (k s) i) := by
  simpa [boundedBranchingBinaryCode] using
    boundedBranchingBinaryCodeFrom_append_singleton k [] s i

theorem boundedBranchingBinaryCode_length_ge {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) :
    ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k →
      s.length ≤ (boundedBranchingBinaryCode k s).length := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
      intro _hs
      simp [boundedBranchingBinaryCode, boundedBranchingBinaryCodeFrom]
  | append_singleton t i ih =>
      intro hs
      have hsplit :
          t ∈ boundedBranchingTree k ∧ i < k t := by
        exact (boundedBranchingTree_child_mem_iff k t i).1 (by simpa [concat] using hs)
      have hchild_pos : 0 < (binaryChildCode (k t) i).length :=
        binaryChildCode_length_pos (hk hsplit.1) hsplit.2
      rw [boundedBranchingBinaryCode_concat]
      simp [concat]
      have iht := ih hsplit.1
      omega

theorem cyl_concat_binaryChildCode_iUnion (q : finseq Bool) {m : ℕ} (hm : 2 ≤ m) :
    cyl q = ⋃ i : {i : ℕ // i < m}, cyl (concat q (binaryChildCode m i.1)) := by
  ext x
  constructor
  · intro hxq
    obtain ⟨i, hitail⟩ :=
      exists_mem_cyl_binaryChildCode m hm (fun n : ℕ => x (q.length + n))
    exact Set.mem_iUnion.2 ⟨i, (mem_cyl_concat_iff (s := q)
      (t := binaryChildCode m i.1) (x := x)).2 ⟨hxq, hitail⟩⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    exact ((mem_cyl_concat_iff (s := q) (t := binaryChildCode m i.1) (x := x)).1 hxi).1

theorem cyl_concat_binaryChildCode_disjoint (q : finseq Bool) {m i j : ℕ}
    (hm : 2 ≤ m) (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    Disjoint (cyl (concat q (binaryChildCode m i)))
      (cyl (concat q (binaryChildCode m j))) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have htail_i :
      (fun n : ℕ => x (q.length + n)) ∈ cyl (binaryChildCode m i) :=
    ((mem_cyl_concat_iff (s := q) (t := binaryChildCode m i) (x := x)).1 hxi).2
  have htail_j :
      (fun n : ℕ => x (q.length + n)) ∈ cyl (binaryChildCode m j) :=
    ((mem_cyl_concat_iff (s := q) (t := binaryChildCode m j) (x := x)).1 hxj).2
  exact (Set.disjoint_left.mp (cyl_binaryChildCode_disjoint hm hi hj hij)) htail_i htail_j

structure ClopenSchemeCore {X : Type u} [TopologicalSpace X]
    (T : Set (finseq ℕ)) (U : finseq ℕ → Set X) : Prop where
  root_mem : ([] : finseq ℕ) ∈ T
  root_eq : U [] = Set.univ
  nonempty : ∀ ⦃s : finseq ℕ⦄, s ∈ T → (U s).Nonempty
  clopen : ∀ ⦃s : finseq ℕ⦄, s ∈ T → IsClopen (U s)
  children_cover : ∀ ⦃s : finseq ℕ⦄, s ∈ T →
    U s = ⋃ i : {i : ℕ // concat s [i] ∈ T}, U (concat s [i.1])
  children_disjoint : ∀ ⦃s : finseq ℕ⦄, (hs : s ∈ T) →
    ∀ i j : {i : ℕ // concat s [i] ∈ T}, i ≠ j →
      Disjoint (U (concat s [i.1])) (U (concat s [j.1]))

structure ClopenSchemeMetricCore {X : Type u} [PseudoMetricSpace X]
    (T : Set (finseq ℕ)) (U : finseq ℕ → Set X) : Prop
    extends ClopenSchemeCore T U where
  dist_bound : ∀ ⦃s : finseq ℕ⦄, s ∈ T →
    ∀ x ∈ U s, ∀ y ∈ U s, dist x y ≤ (1 / 2 : ℝ) ^ s.length

structure BoundedBranchingSchemeCore {X : Type u} [PseudoMetricSpace X]
    (k : finseq ℕ → ℕ) (U : finseq ℕ → Set X) : Prop where
  root_eq : U [] = Set.univ
  nonempty : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → (U s).Nonempty
  clopen : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → IsClopen (U s)
  children_cover : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k →
    U s = ⋃ i : {i : ℕ // i < k s}, U (concat s [i.1])
  children_disjoint : ∀ ⦃s : finseq ℕ⦄, (hs : s ∈ boundedBranchingTree k) →
    ∀ i j : {i : ℕ // i < k s}, i ≠ j →
      Disjoint (U (concat s [i.1])) (U (concat s [j.1]))
  dist_bound : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k →
    ∀ x ∈ U s, ∀ y ∈ U s, dist x y ≤ (1 / 2 : ℝ) ^ s.length

theorem boundedBranchingSchemeCore_to_clopenSchemeMetricCore {X : Type u}
    [PseudoMetricSpace X] {k : finseq ℕ → ℕ} {U : finseq ℕ → Set X}
    (H : BoundedBranchingSchemeCore k U) :
    ClopenSchemeMetricCore (boundedBranchingTree k) U where
  root_mem := mem_boundedBranchingTree_nil k
  root_eq := H.root_eq
  nonempty := H.nonempty
  clopen := H.clopen
  children_cover := by
    intro s hs
    rw [H.children_cover hs]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2
        ⟨⟨i.1, boundedBranchingTree_child_mem hs i.2⟩, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      have hi : i.1 < k s := boundedBranchingTree_lt_of_child_mem i.2
      exact Set.mem_iUnion.2 ⟨⟨i.1, hi⟩, hxi⟩
  children_disjoint := by
    intro s hs i j hij
    have hi : i.1 < k s := boundedBranchingTree_lt_of_child_mem i.2
    have hj : j.1 < k s := boundedBranchingTree_lt_of_child_mem j.2
    exact H.children_disjoint hs ⟨i.1, hi⟩ ⟨j.1, hj⟩ (by
      intro h
      have hval : i.1 = j.1 := congrArg (fun q : {i : ℕ // i < k s} => q.1) h
      exact hij (Subtype.ext hval))
  dist_bound := H.dist_bound

theorem clopenSchemeCore_child_subset {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U)
    {s : finseq ℕ} {i : ℕ} (hsi : concat s [i] ∈ T) :
    U (concat s [i]) ⊆ U s := by
  have hs : s ∈ T := hT hsi (by
    change s <+: s ++ [i]
    exact s.prefix_append [i])
  intro x hx
  rw [H.children_cover hs]
  exact Set.mem_iUnion.2 ⟨⟨i, hsi⟩, hx⟩

theorem clopenSchemeCore_sibling_disjoint {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) {s : finseq ℕ} (hs : s ∈ T)
    {i j : ℕ} (hsi : concat s [i] ∈ T) (hsj : concat s [j] ∈ T) (hij : i ≠ j) :
    Disjoint (U (concat s [i])) (U (concat s [j])) := by
  exact H.children_disjoint hs ⟨i, hsi⟩ ⟨j, hsj⟩ (by
    intro h
    exact hij (congrArg Subtype.val h))

theorem clopenSchemeCore_concat_subset {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U)
    {s r : finseq ℕ} (hsr : concat s r ∈ T) :
    U (concat s r) ⊆ U s := by
  induction r generalizing s with
  | nil =>
      simp [concat]
  | cons i r ih =>
      have hconcat :
          concat s (i :: r) = concat (concat s [i]) r := by
        simp [concat, List.append_assoc]
      have hp : prefixOf (concat s [i]) (concat s (i :: r)) := by
        change s ++ [i] <+: s ++ (i :: r)
        rw [show s ++ (i :: r) = (s ++ [i]) ++ r by simp]
        exact (s ++ [i]).prefix_append r
      have hchild : concat s [i] ∈ T := hT hsr hp
      have htail_mem : concat (concat s [i]) r ∈ T := by
        rw [← hconcat]
        exact hsr
      rw [hconcat]
      exact (ih htail_mem).trans (clopenSchemeCore_child_subset hT H hchild)

theorem clopenSchemeCore_prefix_subset {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U)
    {s t : finseq ℕ} (ht : t ∈ T) (hst : prefixOf s t) :
    U t ⊆ U s := by
  have ht_eq : concat s (t.drop s.length) = t := by
    simpa [concat] using (List.prefix_append_drop hst).symm
  have ht' : concat s (t.drop s.length) ∈ T := by
    rwa [ht_eq]
  simpa [ht_eq] using
    clopenSchemeCore_concat_subset (hT := hT) (H := H) ht'

theorem clopenSchemeCore_branch_mem {T : Set (finseq ℕ)} {b : ℕ → ℕ}
    (hb : b ∈ treeBody T) (n : ℕ) :
    seqPrefix b n ∈ T :=
  hb n

theorem clopenSchemeCore_branch_subset {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U)
    {b : ℕ → ℕ} (hb : b ∈ treeBody T) {n m : ℕ} (hnm : n ≤ m) :
    U (seqPrefix b m) ⊆ U (seqPrefix b n) :=
  clopenSchemeCore_prefix_subset (hT := hT) (H := H)
    (clopenSchemeCore_branch_mem hb m) (seqPrefix_prefixOf_of_le b hnm)

theorem clopenSchemeCore_branch_nonempty {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) (n : ℕ) :
    (U (seqPrefix b n)).Nonempty :=
  H.nonempty (clopenSchemeCore_branch_mem hb n)

theorem clopenSchemeCore_branch_isClosed {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) (n : ℕ) :
    IsClosed (U (seqPrefix b n)) :=
  (H.clopen (clopenSchemeCore_branch_mem hb n)).isClosed

theorem clopenSchemeMetricCore_branch_dist_le {X : Type u} [PseudoMetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeMetricCore T U)
    {b : ℕ → ℕ} (hb : b ∈ treeBody T) {n m : ℕ} (hnm : n ≤ m)
    {x y : X} (hx : x ∈ U (seqPrefix b m)) (hy : y ∈ U (seqPrefix b n)) :
    dist x y ≤ (1 / 2 : ℝ) ^ n := by
  have hx' : x ∈ U (seqPrefix b n) :=
    clopenSchemeCore_branch_subset (hT := hT) (H := H.toClopenSchemeCore) hb hnm hx
  simpa [seqPrefix_length] using
    H.dist_bound (clopenSchemeCore_branch_mem hb n) x hx' y hy

theorem clopenSchemeMetricCore_branch_sample_cauchy {X : Type u} [PseudoMetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeMetricCore T U)
    {b : ℕ → ℕ} (hb : b ∈ treeBody T) {a : ℕ → X}
    (ha : ∀ n : ℕ, a n ∈ U (seqPrefix b n)) :
    CauchySeq a := by
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => (1 / 2 : ℝ) ^ N) ?_ ?_
  · intro n m N hNn hNm
    have hnU : a n ∈ U (seqPrefix b N) :=
      clopenSchemeCore_branch_subset (hT := hT) (H := H.toClopenSchemeCore) hb hNn (ha n)
    have hmU : a m ∈ U (seqPrefix b N) :=
      clopenSchemeCore_branch_subset (hT := hT) (H := H.toClopenSchemeCore) hb hNm (ha m)
    simpa [seqPrefix_length] using
      H.dist_bound (clopenSchemeCore_branch_mem hb N) (a n) hnU (a m) hmU
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)

noncomputable def clopenSchemeCore_branchSample {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) :
    ℕ → X :=
  fun n => Classical.choose (clopenSchemeCore_branch_nonempty H hb n)

theorem clopenSchemeCore_branchSample_mem {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) (n : ℕ) :
    clopenSchemeCore_branchSample H hb n ∈ U (seqPrefix b n) :=
  Classical.choose_spec (clopenSchemeCore_branch_nonempty H hb n)

theorem clopenSchemeMetricCore_branchSample_cauchy {X : Type u} [PseudoMetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeMetricCore T U)
    {b : ℕ → ℕ} (hb : b ∈ treeBody T) :
    CauchySeq (clopenSchemeCore_branchSample H.toClopenSchemeCore hb) :=
  clopenSchemeMetricCore_branch_sample_cauchy (hT := hT) (H := H) hb
    (clopenSchemeCore_branchSample_mem H.toClopenSchemeCore hb)

theorem clopenSchemeMetricCore_branchSample_exists_limit {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) :
    ∃ x : X, Filter.Tendsto (clopenSchemeCore_branchSample H.toClopenSchemeCore hb)
      Filter.atTop (𝓝 x) :=
  hcomplete _ (clopenSchemeMetricCore_branchSample_cauchy (hT := hT) (H := H) hb)

theorem clopenSchemeCore_branchSample_limit_mem {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U)
    {b : ℕ → ℕ} (hb : b ∈ treeBody T) {x : X}
    (hxlim : Filter.Tendsto (clopenSchemeCore_branchSample H hb) Filter.atTop (𝓝 x)) (n : ℕ) :
    x ∈ U (seqPrefix b n) := by
  refine (clopenSchemeCore_branch_isClosed H hb n).mem_of_tendsto hxlim ?_
  exact (Filter.eventually_ge_atTop n).mono fun m hm =>
    clopenSchemeCore_branch_subset (hT := hT) (H := H) hb hm
      (clopenSchemeCore_branchSample_mem H hb m)

theorem clopenSchemeMetricCore_branchSample_exists_limit_mem {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) :
    ∃ x : X,
      Filter.Tendsto (clopenSchemeCore_branchSample H.toClopenSchemeCore hb) Filter.atTop (𝓝 x) ∧
        ∀ n : ℕ, x ∈ U (seqPrefix b n) := by
  rcases clopenSchemeMetricCore_branchSample_exists_limit
    (hcomplete := hcomplete) (hT := hT) (H := H) hb with ⟨x, hxlim⟩
  exact ⟨x, hxlim, fun n =>
    clopenSchemeCore_branchSample_limit_mem (hT := hT) H.toClopenSchemeCore hb hxlim n⟩

theorem clopenSchemeMetricCore_branch_points_eq {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeMetricCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T)
    {x y : X} (hx : ∀ n : ℕ, x ∈ U (seqPrefix b n))
    (hy : ∀ n : ℕ, y ∈ U (seqPrefix b n)) :
    x = y := by
  by_contra hxy
  have hdist_pos : 0 < dist x y := (dist_pos).2 hxy
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one hdist_pos (by norm_num : (1 / 2 : ℝ) < 1)
  have hle : dist x y ≤ (1 / 2 : ℝ) ^ N := by
    simpa [seqPrefix_length] using
      H.dist_bound (clopenSchemeCore_branch_mem hb N) x (hx N) y (hy N)
  exact not_lt_of_ge hle hN

theorem clopenSchemeMetricCore_branch_iInter_subsingleton {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeMetricCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) :
    (⋂ n : ℕ, U (seqPrefix b n)).Subsingleton := by
  intro x hx y hy
  exact clopenSchemeMetricCore_branch_points_eq (H := H) hb
    (fun n => Set.mem_iInter.1 hx n) (fun n => Set.mem_iInter.1 hy n)

theorem clopenSchemeMetricCore_branch_iInter_eq_singleton {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) {b : ℕ → ℕ} (hb : b ∈ treeBody T) :
    ∃ x : X,
      (⋂ n : ℕ, U (seqPrefix b n)) = {x} ∧
        Filter.Tendsto (clopenSchemeCore_branchSample H.toClopenSchemeCore hb) Filter.atTop
          (𝓝 x) := by
  rcases clopenSchemeMetricCore_branchSample_exists_limit_mem
    (hcomplete := hcomplete) (hT := hT) (H := H) hb with ⟨x, hxlim, hxmem⟩
  refine ⟨x, ?_, hxlim⟩
  exact (clopenSchemeMetricCore_branch_iInter_subsingleton (H := H) hb).eq_singleton_of_mem
    (Set.mem_iInter.2 hxmem)

noncomputable def clopenSchemeMetricCore_branchPoint {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) (b : treeBody T) : X :=
  Classical.choose (clopenSchemeMetricCore_branch_iInter_eq_singleton
    (hcomplete := hcomplete) (hT := hT) (H := H) b.2)

theorem clopenSchemeMetricCore_branchPoint_iInter_eq_singleton {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) (b : treeBody T) :
    (⋂ n : ℕ, U (seqPrefix (b : ℕ → ℕ) n)) =
      {clopenSchemeMetricCore_branchPoint hcomplete hT H b} :=
  (Classical.choose_spec (clopenSchemeMetricCore_branch_iInter_eq_singleton
    (hcomplete := hcomplete) (hT := hT) (H := H) b.2)).1

theorem clopenSchemeMetricCore_branchPoint_tendsto_sample {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) (b : treeBody T) :
    Filter.Tendsto (clopenSchemeCore_branchSample H.toClopenSchemeCore b.2) Filter.atTop
      (𝓝 (clopenSchemeMetricCore_branchPoint hcomplete hT H b)) :=
  (Classical.choose_spec (clopenSchemeMetricCore_branch_iInter_eq_singleton
    (hcomplete := hcomplete) (hT := hT) (H := H) b.2)).2

theorem clopenSchemeMetricCore_branchPoint_mem {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) (b : treeBody T) (n : ℕ) :
    clopenSchemeMetricCore_branchPoint hcomplete hT H b ∈ U (seqPrefix (b : ℕ → ℕ) n) := by
  have hmem :
      clopenSchemeMetricCore_branchPoint hcomplete hT H b ∈
        (⋂ n : ℕ, U (seqPrefix (b : ℕ → ℕ) n)) := by
    rw [clopenSchemeMetricCore_branchPoint_iInter_eq_singleton
      (hcomplete := hcomplete) (hT := hT) (H := H) b]
    simp
  exact Set.mem_iInter.1 hmem n

theorem continuous_clopenSchemeMetricCore_branchPoint {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) :
    Continuous fun b : treeBody T => clopenSchemeMetricCore_branchPoint hcomplete hT H b := by
  rw [continuous_iff_continuousAt]
  intro b
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hprefix_nhds :
      {c : treeBody T | (c : ℕ → ℕ) ∈ cyl (seqPrefix (b : ℕ → ℕ) N)} ∈ 𝓝 b := by
    exact ((isOpen_cyl (A := ℕ) (seqPrefix (b : ℕ → ℕ) N)).preimage
      continuous_subtype_val).mem_nhds (mem_cyl_seqPrefix (b : ℕ → ℕ) N)
  refine Filter.mem_of_superset hprefix_nhds ?_
  · intro c hc
    have hc_prefix :
        seqPrefix (c : ℕ → ℕ) N = seqPrefix (b : ℕ → ℕ) N :=
      by simpa [seqPrefix_length] using seqPrefix_eq_of_mem_cyl hc
    have hb_mem :
        clopenSchemeMetricCore_branchPoint hcomplete hT H b ∈
          U (seqPrefix (b : ℕ → ℕ) N) :=
      clopenSchemeMetricCore_branchPoint_mem hcomplete hT H b N
    have hc_mem :
        clopenSchemeMetricCore_branchPoint hcomplete hT H c ∈
          U (seqPrefix (b : ℕ → ℕ) N) := by
      simpa [hc_prefix] using
        clopenSchemeMetricCore_branchPoint_mem hcomplete hT H c N
    have hle :
        dist (clopenSchemeMetricCore_branchPoint hcomplete hT H c)
          (clopenSchemeMetricCore_branchPoint hcomplete hT H b) ≤ (1 / 2 : ℝ) ^ N := by
      simpa [seqPrefix_length] using
        H.dist_bound (b.2 N)
          (clopenSchemeMetricCore_branchPoint hcomplete hT H c) hc_mem
          (clopenSchemeMetricCore_branchPoint hcomplete hT H b) hb_mem
    exact lt_of_le_of_lt hle hN

theorem clopenSchemeMetricCore_branchPoint_injective {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) :
    Function.Injective fun b : treeBody T =>
      clopenSchemeMetricCore_branchPoint hcomplete hT H b := by
  intro b c hpoint
  apply Subtype.ext
  by_contra hbc
  let k : ℕ := firstDiffIndex (b : ℕ → ℕ) (c : ℕ → ℕ)
  have hdiff : (b : ℕ → ℕ) k ≠ (c : ℕ → ℕ) k :=
    firstDiffIndex_spec hbc
  have hagree : agreeOnPrefix k (b : ℕ → ℕ) (c : ℕ → ℕ) :=
    agreeOnPrefix_of_le_firstDiffIndex hbc le_rfl
  have hprefix_eq :
      seqPrefix (c : ℕ → ℕ) k = seqPrefix (b : ℕ → ℕ) k := by
    unfold seqPrefix
    rw [List.ofFn_inj]
    funext i
    exact (hagree i i.2).symm
  have hb_child_mem :
      concat (seqPrefix (b : ℕ → ℕ) k) [(b : ℕ → ℕ) k] ∈ T := by
    simpa [k, seqPrefix_succ_eq_concat] using b.2 (k + 1)
  have hc_child_mem :
      concat (seqPrefix (b : ℕ → ℕ) k) [(c : ℕ → ℕ) k] ∈ T := by
    have hc_succ := c.2 (k + 1)
    simpa [k, seqPrefix_succ_eq_concat, hprefix_eq] using hc_succ
  have hb_point_child :
      clopenSchemeMetricCore_branchPoint hcomplete hT H b ∈
        U (concat (seqPrefix (b : ℕ → ℕ) k) [(b : ℕ → ℕ) k]) := by
    simpa [k, seqPrefix_succ_eq_concat] using
      clopenSchemeMetricCore_branchPoint_mem hcomplete hT H b (k + 1)
  have hc_point_child :
      clopenSchemeMetricCore_branchPoint hcomplete hT H c ∈
        U (concat (seqPrefix (b : ℕ → ℕ) k) [(c : ℕ → ℕ) k]) := by
    simpa [k, seqPrefix_succ_eq_concat, hprefix_eq] using
      clopenSchemeMetricCore_branchPoint_mem hcomplete hT H c (k + 1)
  have hdisj :
      Disjoint (U (concat (seqPrefix (b : ℕ → ℕ) k) [(b : ℕ → ℕ) k]))
        (U (concat (seqPrefix (b : ℕ → ℕ) k) [(c : ℕ → ℕ) k])) :=
    clopenSchemeCore_sibling_disjoint H.toClopenSchemeCore (b.2 k)
      hb_child_mem hc_child_mem hdiff
  exact (Set.disjoint_left.mp hdisj) hb_point_child (by simpa [hpoint] using hc_point_child)

theorem clopenSchemeCore_exists_child_mem {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) {s : finseq ℕ} (hs : s ∈ T)
    {z : X} (hz : z ∈ U s) :
    ∃ i : ℕ, concat s [i] ∈ T ∧ z ∈ U (concat s [i]) := by
  have hz' :
      z ∈ ⋃ i : {i : ℕ // concat s [i] ∈ T}, U (concat s [i.1]) := by
    simpa [H.children_cover hs] using hz
  rcases Set.mem_iUnion.1 hz' with ⟨i, hi⟩
  exact ⟨i.1, i.2, hi⟩

noncomputable def clopenSchemeCore_pointNode {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) :
    ℕ → {s : finseq ℕ // s ∈ T ∧ z ∈ U s}
  | 0 => ⟨[], H.root_mem, by simp [H.root_eq]⟩
  | n + 1 =>
      let q := clopenSchemeCore_pointNode H z n
      let i := Classical.choose (clopenSchemeCore_exists_child_mem H q.2.1 q.2.2)
      have hi := Classical.choose_spec (clopenSchemeCore_exists_child_mem H q.2.1 q.2.2)
      ⟨concat q.1 [i], hi.1, hi.2⟩

theorem clopenSchemeCore_pointNode_length {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) (n : ℕ) :
    (clopenSchemeCore_pointNode H z n).1.length = n := by
  induction n with
  | zero =>
      simp [clopenSchemeCore_pointNode]
  | succ n ih =>
      simp [clopenSchemeCore_pointNode, concat, ih]

noncomputable def clopenSchemeCore_pointBranch {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) : ℕ → ℕ :=
  fun n =>
    (clopenSchemeCore_pointNode H z (n + 1)).1.get ⟨n, by
      simp [clopenSchemeCore_pointNode_length H z (n + 1)]⟩

theorem clopenSchemeCore_pointNode_succ_eq_concat {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) (n : ℕ) :
    (clopenSchemeCore_pointNode H z (n + 1)).1 =
      concat (clopenSchemeCore_pointNode H z n).1 [clopenSchemeCore_pointBranch H z n] := by
  simp [clopenSchemeCore_pointBranch, clopenSchemeCore_pointNode, concat,
    clopenSchemeCore_pointNode_length]

theorem clopenSchemeCore_seqPrefix_pointBranch_eq_pointNode {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) (n : ℕ) :
    seqPrefix (clopenSchemeCore_pointBranch H z) n =
      (clopenSchemeCore_pointNode H z n).1 := by
  induction n with
  | zero =>
      simp [seqPrefix, clopenSchemeCore_pointNode]
  | succ n ih =>
      rw [seqPrefix_succ_eq_concat, ih,
        clopenSchemeCore_pointNode_succ_eq_concat H z n]

theorem clopenSchemeCore_pointBranch_mem_treeBody {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) :
    clopenSchemeCore_pointBranch H z ∈ treeBody T := by
  intro n
  rw [clopenSchemeCore_seqPrefix_pointBranch_eq_pointNode H z n]
  exact (clopenSchemeCore_pointNode H z n).2.1

theorem clopenSchemeCore_pointBranch_point_mem {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) (n : ℕ) :
    z ∈ U (seqPrefix (clopenSchemeCore_pointBranch H z) n) := by
  rw [clopenSchemeCore_seqPrefix_pointBranch_eq_pointNode H z n]
  exact (clopenSchemeCore_pointNode H z n).2.2

theorem clopenSchemeCore_pointNode_eq_of_mem_pointNode {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U)
    {z y : X} (n : ℕ) (hy_mem : y ∈ U (clopenSchemeCore_pointNode H z n).1) :
    (clopenSchemeCore_pointNode H y n).1 = (clopenSchemeCore_pointNode H z n).1 := by
  induction n with
  | zero =>
      simp [clopenSchemeCore_pointNode]
  | succ n ih =>
      have hz_succ_eq := clopenSchemeCore_pointNode_succ_eq_concat H z n
      have hy_succ_eq := clopenSchemeCore_pointNode_succ_eq_concat H y n
      have hz_child_mem :
          concat (clopenSchemeCore_pointNode H z n).1 [clopenSchemeCore_pointBranch H z n] ∈ T := by
        simpa [← hz_succ_eq] using (clopenSchemeCore_pointNode H z (n + 1)).2.1
      have hy_in_z_child :
          y ∈ U (concat (clopenSchemeCore_pointNode H z n).1
            [clopenSchemeCore_pointBranch H z n]) := by
        simpa [hz_succ_eq] using hy_mem
      have hy_parent : y ∈ U (clopenSchemeCore_pointNode H z n).1 :=
        clopenSchemeCore_child_subset hT H hz_child_mem hy_in_z_child
      have hnode_n :
          (clopenSchemeCore_pointNode H y n).1 = (clopenSchemeCore_pointNode H z n).1 :=
        ih hy_parent
      have hy_child_mem :
          concat (clopenSchemeCore_pointNode H z n).1 [clopenSchemeCore_pointBranch H y n] ∈ T := by
        have hy_succ_mem := (clopenSchemeCore_pointNode H y (n + 1)).2.1
        simpa [hy_succ_eq, hnode_n] using hy_succ_mem
      have hy_in_y_child :
          y ∈ U (concat (clopenSchemeCore_pointNode H z n).1
            [clopenSchemeCore_pointBranch H y n]) := by
        have hy_succ_mem := (clopenSchemeCore_pointNode H y (n + 1)).2.2
        simpa [hy_succ_eq, hnode_n] using hy_succ_mem
      have hindex :
          clopenSchemeCore_pointBranch H y n = clopenSchemeCore_pointBranch H z n := by
        by_contra hneq
        have hdisj :
            Disjoint (U (concat (clopenSchemeCore_pointNode H z n).1
              [clopenSchemeCore_pointBranch H y n]))
              (U (concat (clopenSchemeCore_pointNode H z n).1
                [clopenSchemeCore_pointBranch H z n])) :=
          clopenSchemeCore_sibling_disjoint H (clopenSchemeCore_pointNode H z n).2.1
            hy_child_mem hz_child_mem hneq
        exact (Set.disjoint_left.mp hdisj) hy_in_y_child hy_in_z_child
      rw [hy_succ_eq, hz_succ_eq, hnode_n, hindex]

noncomputable def clopenSchemeCore_pointBranchInTree {X : Type u} [TopologicalSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (H : ClopenSchemeCore T U) (z : X) : treeBody T :=
  ⟨clopenSchemeCore_pointBranch H z, clopenSchemeCore_pointBranch_mem_treeBody H z⟩

theorem continuous_clopenSchemeCore_pointBranchInTree {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hT : IsSubtree T) (H : ClopenSchemeCore T U) :
    Continuous fun z : X => clopenSchemeCore_pointBranchInTree H z := by
  refine Continuous.subtype_mk ?_ _
  rw [continuous_iff_continuousAt]
  intro z
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨n, hn⟩ :=
    exists_cyl_subset_seqMetric_ball (A := ℕ)
      (x := clopenSchemeCore_pointBranch H z) hε
  have hnode_open : IsOpen (U (clopenSchemeCore_pointNode H z (n + 1)).1) :=
    (H.clopen (clopenSchemeCore_pointNode H z (n + 1)).2.1).isOpen
  have hz_node : z ∈ U (clopenSchemeCore_pointNode H z (n + 1)).1 :=
    (clopenSchemeCore_pointNode H z (n + 1)).2.2
  refine Filter.mem_of_superset (hnode_open.mem_nhds hz_node) ?_
  · intro y hy
    have hnode_eq :
        (clopenSchemeCore_pointNode H y (n + 1)).1 =
          (clopenSchemeCore_pointNode H z (n + 1)).1 :=
      clopenSchemeCore_pointNode_eq_of_mem_pointNode hT H (n + 1) hy
    have hprefix_eq :
        seqPrefix (clopenSchemeCore_pointBranch H y) (n + 1) =
          seqPrefix (clopenSchemeCore_pointBranch H z) (n + 1) := by
      rw [clopenSchemeCore_seqPrefix_pointBranch_eq_pointNode H y (n + 1),
        clopenSchemeCore_seqPrefix_pointBranch_eq_pointNode H z (n + 1), hnode_eq]
    have hy_cyl :
        clopenSchemeCore_pointBranch H y ∈
          cyl (seqPrefix (clopenSchemeCore_pointBranch H z) (n + 1)) := by
      rw [← hprefix_eq]
      exact mem_cyl_seqPrefix (clopenSchemeCore_pointBranch H y) (n + 1)
    have hseq :
        seqMetric (clopenSchemeCore_pointBranch H y)
          (clopenSchemeCore_pointBranch H z) < ε := by
      simpa [seqMetric_symm] using hn hy_cyl
    have hdist :
        dist (clopenSchemeCore_pointBranch H y : sequence_metric_space ℕ)
          (clopenSchemeCore_pointBranch H z : sequence_metric_space ℕ) < ε := by
      rw [seqMetric_eq_sequenceMetricSpace_dist] at hseq
      exact hseq
    exact hdist

theorem clopenSchemeMetricCore_branchPoint_surjective {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) :
    Function.Surjective fun b : treeBody T =>
      clopenSchemeMetricCore_branchPoint hcomplete hT H b := by
  intro z
  let bseq : ℕ → ℕ := clopenSchemeCore_pointBranch H.toClopenSchemeCore z
  have hbseq : bseq ∈ treeBody T :=
    clopenSchemeCore_pointBranch_mem_treeBody H.toClopenSchemeCore z
  let b : treeBody T := ⟨bseq, hbseq⟩
  have hbranch_mem :
      ∀ n : ℕ, z ∈ U (seqPrefix (b : ℕ → ℕ) n) :=
    clopenSchemeCore_pointBranch_point_mem H.toClopenSchemeCore z
  refine ⟨b, ?_⟩
  exact clopenSchemeMetricCore_branch_points_eq (H := H) b.2
    (clopenSchemeMetricCore_branchPoint_mem hcomplete hT H b) hbranch_mem

theorem clopenSchemeMetricCore_branchPoint_pointBranchInTree {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) (z : X) :
    clopenSchemeMetricCore_branchPoint hcomplete hT H
      (clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z) = z := by
  have hbranch_mem :
      ∀ n : ℕ,
        z ∈ U (seqPrefix
          (clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z : ℕ → ℕ) n) :=
    clopenSchemeCore_pointBranch_point_mem H.toClopenSchemeCore z
  exact clopenSchemeMetricCore_branch_points_eq (H := H)
    (clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z).2
    (clopenSchemeMetricCore_branchPoint_mem hcomplete hT H
      (clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z))
    hbranch_mem

theorem clopenSchemeMetricCore_branchPoint_bijective {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) :
    Function.Bijective fun b : treeBody T =>
      clopenSchemeMetricCore_branchPoint hcomplete hT H b :=
  ⟨clopenSchemeMetricCore_branchPoint_injective hcomplete hT H,
    clopenSchemeMetricCore_branchPoint_surjective hcomplete hT H⟩

noncomputable def clopenSchemeMetricCore_branchPointEquiv {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) :
    treeBody T ≃ X :=
  Equiv.ofBijective (fun b : treeBody T =>
    clopenSchemeMetricCore_branchPoint hcomplete hT H b)
    (clopenSchemeMetricCore_branchPoint_bijective hcomplete hT H)

theorem clopenSchemeMetricCore_branchPointEquiv_symm_apply {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) (z : X) :
    (clopenSchemeMetricCore_branchPointEquiv hcomplete hT H).symm z =
      clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z := by
  apply clopenSchemeMetricCore_branchPoint_injective hcomplete hT H
  calc
    clopenSchemeMetricCore_branchPoint hcomplete hT H
        ((clopenSchemeMetricCore_branchPointEquiv hcomplete hT H).symm z) = z := by
      change (clopenSchemeMetricCore_branchPointEquiv hcomplete hT H)
        ((clopenSchemeMetricCore_branchPointEquiv hcomplete hT H).symm z) = z
      exact Equiv.apply_symm_apply (clopenSchemeMetricCore_branchPointEquiv hcomplete hT H) z
    _ = clopenSchemeMetricCore_branchPoint hcomplete hT H
        (clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z) :=
      (clopenSchemeMetricCore_branchPoint_pointBranchInTree hcomplete hT H z).symm

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: lemma
  title: Clopen-scheme lemma
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $b\in\TreeBody{T}$, the sets $U_{\restrict{b}{n}}$ are nested, closed, nonempty, and have diameters tending to $0$.
    Choose $a_n\in U_{\restrict{b}{n}}$. Then $\Sequence{a_n}{n\in\omega}$ is Cauchy, hence converges to some point of $X$.
    Since each
    $U_{\restrict{b}{n}}$ is closed, the limit lies in every $U_{\restrict{b}{n}}$; uniqueness follows from the shrinking
    diameters. Define
    $$
    h(b)=\text{the unique point of }\bigcap_n U_{\restrict{b}{n}}.
    $$

    \begin{itemize}
    \item \emph{Surjectivity}: given $z\in X$, start with $s_0=\emptySeq$ and choose the unique successor $s_{n+1}$ of $s_n$
    with $z\in U_{s_{n+1}}$. The compatible nodes define a branch $b\in\TreeBody{T}$, and
    $z\in\bigcap_n U_{\restrict{b}{n}}=\{h(b)\}$.
    \item \emph{Injectivity}: if $b\ne c$, take the first coordinate at which they differ. The corresponding one-step
    extensions of their common prefix are distinct sibling nodes, so $h(b)$ and $h(c)$ lie in disjoint clopen pieces.
    \item \emph{Continuity of $h$}: if $\restrict{b}{n}=\restrict{c}{n}$, then $h(b)$ and $h(c)$ lie in the same set
    $U_{\restrict{b}{n}}$, whose diameter is at most $2^{-n}$.
    \item \emph{Continuity of $h^{-1}$}: for $s\in T$, the same branch construction starting inside $U_s$ shows that the
    image of the tree cylinder $\{b\in\TreeBody{T}:s\prefixOf b\}$ is exactly $U_s$, which is open in $X$.
    \end{itemize}

    Thus $h$ is a homeomorphism from $\TreeBody{T}$ onto $X$.
    \end{proof}
-/
noncomputable def clopenSchemeMetricCore_branchPointHomeomorph {X : Type u} [MetricSpace X]
    {T : Set (finseq ℕ)} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (hT : IsSubtree T)
    (H : ClopenSchemeMetricCore T U) :
    treeBody T ≃ₜ X where
  toEquiv := clopenSchemeMetricCore_branchPointEquiv hcomplete hT H
  continuous_toFun := by
    change Continuous fun b : treeBody T => clopenSchemeMetricCore_branchPoint hcomplete hT H b
    exact continuous_clopenSchemeMetricCore_branchPoint hcomplete hT H
  continuous_invFun := by
    change Continuous fun z : X => (clopenSchemeMetricCore_branchPointEquiv hcomplete hT H).symm z
    rw [show (clopenSchemeMetricCore_branchPointEquiv hcomplete hT H).symm =
        fun z : X => clopenSchemeCore_pointBranchInTree H.toClopenSchemeCore z by
      funext z
      exact clopenSchemeMetricCore_branchPointEquiv_symm_apply hcomplete hT H z]
    exact continuous_clopenSchemeCore_pointBranchInTree hT H.toClopenSchemeCore

noncomputable def boundedBranchingSchemeCore_homeomorph {X : Type u} [MetricSpace X]
    {k : finseq ℕ → ℕ} {U : finseq ℕ → Set X}
    (hcomplete : IsMetricComplete X) (H : BoundedBranchingSchemeCore k U) :
    treeBody (boundedBranchingTree k) ≃ₜ X :=
  clopenSchemeMetricCore_branchPointHomeomorph hcomplete
    (boundedBranchingTree_isSubtree k)
    (boundedBranchingSchemeCore_to_clopenSchemeMetricCore H)

section BoundedBranchingCantorScheme

noncomputable local instance cantorPiNatMetricSpace : MetricSpace cantor_space :=
  PiNat.metricSpaceOfDiscreteUniformity (E := fun _ : ℕ => Bool) fun _ => rfl

/-- The Cantor-space cylinders assigned to a bounded-branching tree by the canonical binary
prefix-code partition. -/
noncomputable def boundedBranchingCantorSchemeU (k : finseq ℕ → ℕ) :
    finseq ℕ → Set cantor_space :=
  fun s => cyl (boundedBranchingBinaryCode k s)

theorem cantor_cyl_dist_le_of_mem {q : finseq Bool} {x y : cantor_space}
    (hx : x ∈ cyl q) (hy : y ∈ cyl q) :
    dist x y ≤ (1 / 2 : ℝ) ^ q.length := by
  by_cases hxy : x = y
  · subst y
    rw [dist_self]
    positivity
  · have hprefix := (mem_cyl_iff_eq_or_length_le_firstDiffIndex (A := Bool) hx).1 hy
    have hle : q.length ≤ firstDiffIndex x y := by
      rcases hprefix with hxy' | hle
      · exact False.elim (hxy hxy')
      · exact hle
    rw [PiNat.dist_eq_of_ne hxy, ← firstDiffIndex_eq_pinat_firstDiff]
    exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hle

theorem boundedBranchingCantorSchemeCore {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) :
    ClopenSchemeMetricCore (boundedBranchingTree k) (boundedBranchingCantorSchemeU k) where
  root_mem := mem_boundedBranchingTree_nil k
  root_eq := by
    simp [boundedBranchingCantorSchemeU, boundedBranchingBinaryCode,
      boundedBranchingBinaryCodeFrom]
  nonempty := by
    intro s _hs
    exact cyl_nonempty (boundedBranchingBinaryCode k s)
  clopen := by
    intro s _hs
    exact isClopen_cyl (boundedBranchingBinaryCode k s)
  children_cover := by
    intro s hs
    have hpart :=
      cyl_concat_binaryChildCode_iUnion (boundedBranchingBinaryCode k s) (hk hs)
    ext x
    constructor
    · intro hx
      rw [boundedBranchingCantorSchemeU] at hx
      rw [hpart] at hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2
        ⟨⟨i.1, boundedBranchingTree_child_mem hs i.2⟩, by
          simpa [boundedBranchingCantorSchemeU, boundedBranchingBinaryCode_concat] using hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      have hi : i.1 < k s := boundedBranchingTree_lt_of_child_mem i.2
      rw [boundedBranchingCantorSchemeU, hpart]
      exact Set.mem_iUnion.2
        ⟨⟨i.1, hi⟩, by
          simpa [boundedBranchingCantorSchemeU, boundedBranchingBinaryCode_concat] using hxi⟩
  children_disjoint := by
    intro s hs i j hij
    have hi : i.1 < k s := boundedBranchingTree_lt_of_child_mem i.2
    have hj : j.1 < k s := boundedBranchingTree_lt_of_child_mem j.2
    have hij_val : i.1 ≠ j.1 := by
      intro hval
      exact hij (Subtype.ext hval)
    simpa [boundedBranchingCantorSchemeU, boundedBranchingBinaryCode_concat] using
      cyl_concat_binaryChildCode_disjoint (boundedBranchingBinaryCode k s)
        (hk hs) hi hj hij_val
  dist_bound := by
    intro s hs x hx y hy
    have hdist :
        dist x y ≤ (1 / 2 : ℝ) ^ (boundedBranchingBinaryCode k s).length :=
      cantor_cyl_dist_le_of_mem hx hy
    have hlen :
        s.length ≤ (boundedBranchingBinaryCode k s).length :=
      boundedBranchingBinaryCode_length_ge hk hs
    exact hdist.trans
      (pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hlen)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: corollary
  title: Bounded-branching tree bodies
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each $s\in T_k$ has precisely the immediate successors $s\concat(i)$ with $i<k(s)$. Apply the binary prefix coding
    in the proof of Brouwer's characterization.
    \end{proof}
-/
noncomputable def boundedBranchingTreeBodyCantorHomeomorph {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) :
    treeBody (boundedBranchingTree k) ≃ₜ cantor_space := by
  haveI : CompleteSpace cantor_space := inferInstance
  exact clopenSchemeMetricCore_branchPointHomeomorph
    ((isMetricComplete_iff_completeSpace cantor_space).2 inferInstance)
    (boundedBranchingTree_isSubtree k)
    (boundedBranchingCantorSchemeCore hk)

noncomputable def cantorHomeomorphBoundedBranchingTreeBody {k : finseq ℕ → ℕ}
    (hk : ∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) :
    cantor_space ≃ₜ treeBody (boundedBranchingTree k) :=
  (boundedBranchingTreeBodyCantorHomeomorph hk).symm

end BoundedBranchingCantorScheme

theorem treeBody_subset_compl_cyl_of_not_mem {T : Set (finseq A)} {s : finseq A}
    (hs : s ∉ T) :
    treeBody T ⊆ (cyl s)ᶜ := by
  intro x hx hxs
  exact hs (by simpa [seqPrefix_eq_of_mem_cyl hxs] using hx s.length)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    For any set $T\IncludedIn\finseq{\omega}$, its \termdefine{body} is
    $$
    \begin{aligned}
    \TreeBody{T}
    &:=
    \bigcap_{s\notin T}(\SetDifference{\BaireSpace}{\cyl{s}})\\
    &=
    \{x\in\BaireSpace:\restrict{x}{n}\in T\text{ for every }n\in\omega\}.
    \end{aligned}
    $$
    These are the infinite branches through $T$.
-/
theorem treeBody_eq_iInter_compl_cyl (T : Set (finseq A)) :
    treeBody T = ⋂ s : {s : finseq A // s ∉ T}, (cyl s.1)ᶜ := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iInter.2 fun s hxs => treeBody_subset_compl_cyl_of_not_mem s.2 hx hxs
  · intro hx n
    by_contra hnot
    exact (Set.mem_iInter.1 hx ⟨seqPrefix x n, hnot⟩) (mem_cyl_seqPrefix x n)

theorem compl_treeBody_eq_cylinderCode_compl (T : Set (finseq A)) :
    (treeBody T)ᶜ = cylinderCode (Tᶜ) := by
  ext x
  constructor
  · intro hx
    have hx' : ∃ n : ℕ, seqPrefix x n ∉ T := by
      by_contra hnone
      exact hx (fun n => by
        by_contra hn
        exact hnone ⟨n, hn⟩)
    rcases hx' with ⟨n, hn⟩
    exact mem_cylinderCode.2 ⟨seqPrefix x n, hn, mem_cyl_seqPrefix x n⟩
  · intro hx hbody
    rcases mem_cylinderCode.1 hx with ⟨s, hsT, hxs⟩
    exact hsT (by simpa [seqPrefix_eq_of_mem_cyl hxs] using hbody s.length)

theorem isClosed_treeBody [TopologicalSpace A] [DiscreteTopology A] (T : Set (finseq A)) :
    IsClosed (treeBody T) := by
  rw [← isOpen_compl_iff, compl_treeBody_eq_cylinderCode_compl]
  exact isOpen_cylinderCode Tᶜ

theorem subtree_compl_isPrefixUpSet {T : Set (finseq A)} (hT : IsSubtree T) :
    IsPrefixUpSet (Tᶜ) := by
  intro s t hs hst ht
  exact hs (hT ht hst)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    A subtree $T$ is \termdefine{pruned} if every node lies on some branch through $T$:
    for every $s\in T$ there exists $x\in\TreeBody{T}$ with $s\prefixOf x$.
    Since the complement of a downward-closed set is upward-closed, $T$ is pruned exactly when
    $\SetDifference{\finseq{\omega}}{T}$
    is a saturated up-set:
    $$
    \SetDifference{\finseq{\omega}}{T}
    =
    \OpenCylinderCode{\CylinderCode{\SetDifference{\finseq{\omega}}{T}}}.
    $$
    Indeed, suppose first that $T$ is pruned.
    If every branch through $s$ eventually reaches $\SetDifference{\finseq{\omega}}{T}$, then no branch through $T$ extends
    $s$.
    Prunedness therefore forces $s\notin T$, so $s\in\SetDifference{\finseq{\omega}}{T}$.
    Thus the complementary up-set is saturated.
    Conversely, suppose $\SetDifference{\finseq{\omega}}{T}$ is saturated and let $s\in T$.
    If no branch through $T$ extended $s$, then every $x\in\cyl{s}$ would have some prefix outside $T$, so saturation would
    give $s\notin T$, a contradiction.
    Hence some $x\in\TreeBody{T}$ extends $s$, and $T$ is pruned.
-/
theorem isPruned_iff_compl_isSaturated {T : Set (finseq A)} (hT : IsSubtree T) :
    IsPruned T ↔ IsSaturatedPrefixUpSet (Tᶜ) := by
  constructor
  · intro hpruned
    refine ⟨subtree_compl_isPrefixUpSet hT, ?_⟩
    intro s hbranches hsT
    rcases hpruned hsT with ⟨x, hxbody, hxs⟩
    rcases hbranches x hxs with ⟨n, hn⟩
    exact hn (hxbody n)
  · intro hsaturated s hsT
    by_contra hno
    have hbranches : ∀ x : ℕ → A, x ∈ cyl s → ∃ n : ℕ, seqPrefix x n ∈ Tᶜ := by
      intro x hxs
      by_contra hnone
      have hxbody : x ∈ treeBody T := by
        intro n
        by_contra hn
        exact hnone ⟨n, hn⟩
      exact hno ⟨x, hxbody, hxs⟩
    exact (hsaturated.2 s hbranches) hsT

theorem closedTreeCode_isSubtree (F : Set (ℕ → A)) :
    IsSubtree (closedTreeCode F) := by
  intro s t htF hst
  rcases htF with ⟨x, hxt, hxF⟩
  exact ⟨x, cyl_subset_of_prefix hst hxt, hxF⟩

theorem closedTreeCode_isPruned (F : Set (ℕ → A)) :
    IsPruned (closedTreeCode F) := by
  intro s hsF
  rcases hsF with ⟨x, hxs, hxF⟩
  refine ⟨x, ?_, hxs⟩
  intro n
  exact ⟨x, mem_cyl_seqPrefix x n, hxF⟩

theorem subset_treeBody_closedTreeCode (F : Set (ℕ → A)) :
    F ⊆ treeBody (closedTreeCode F) := by
  intro x hxF n
  exact ⟨x, mem_cyl_seqPrefix x n, hxF⟩

theorem treeBody_closedTreeCode_subset_of_closed [TopologicalSpace A] [DiscreteTopology A]
    {F : Set (ℕ → A)} (hF : IsClosed F) :
    treeBody (closedTreeCode F) ⊆ F := by
  intro x hxbody
  by_contra hxF
  have hopen : IsOpen (Fᶜ) := hF.isOpen_compl
  obtain ⟨s, hxs, hsF⟩ := exists_cyl_subset_of_mem_open (A := A) (U := Fᶜ)
    (x := x) hxF hopen
  have hscode : s ∈ closedTreeCode F := by
    simpa [seqPrefix_eq_of_mem_cyl hxs] using hxbody s.length
  rcases hscode with ⟨y, hys, hyF⟩
  exact hsF hys hyF

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\ClosedSets{\BaireSpace}$ is in one-to-one correspondence with the pruned elements of $\PrefixSubtrees{\omega}$, via $T\mapsto\TreeBody{T}$ and $F\mapsto \ClosedTreeCode{F}:=\{s\in\finseq{\omega}:\cyl{s}\cap F\ne\emptyset\}$. \end{claim*}
-/
theorem treeBody_closedTreeCode_eq_of_closed [TopologicalSpace A] [DiscreteTopology A]
    {F : Set (ℕ → A)} (hF : IsClosed F) :
    treeBody (closedTreeCode F) = F := by
  exact Set.Subset.antisymm (treeBody_closedTreeCode_subset_of_closed hF)
    (subset_treeBody_closedTreeCode F)

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\ClosedSets{\BaireSpace}$ is in one-to-one correspondence with the pruned elements of $\PrefixSubtrees{\omega}$, via $T\mapsto\TreeBody{T}$ and $F\mapsto \ClosedTreeCode{F}:=\{s\in\finseq{\omega}:\cyl{s}\cap F\ne\emptyset\}$. \end{claim*}
-/
theorem closedTreeCode_treeBody_eq_of_pruned {T : Set (finseq A)} (hT : IsPruned T) :
    closedTreeCode (treeBody T) = T := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨x, hxs, hxbody⟩
    simpa [seqPrefix_eq_of_mem_cyl hxs] using hxbody s.length
  · intro hsT
    rcases hT hsT with ⟨x, hxbody, hxs⟩
    exact ⟨x, hxs, hxbody⟩

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Let $F\IncludedIn\BaireSpace$ be closed.
    Apply the preceding open-set correspondence to the open complement $\SetDifference{\BaireSpace}{F}$.
    The complementary prefix set is
    $$
    \SetDifference{\finseq{\omega}}{\OpenCylinderCode{\SetDifference{\BaireSpace}{F}}}
    =
    \{s\in\finseq{\omega}:\cyl{s}\cap F\ne\emptyset\}
    =
    \ClosedTreeCode{F}.
    $$
    Thus the closed-set code is the complement of the saturated code for the open complement.
    Since $\OpenCylinderCode{\SetDifference{\BaireSpace}{F}}$ is a saturated up-set, $\ClosedTreeCode{F}$ is a pruned
    subtree by the preceding
    equivalence.
    Moreover, $F=\TreeBody{\ClosedTreeCode{F}}$.
    If $x\in F$, then every cylinder $\cyl{\restrict{x}{n}}$ meets $F$, so every prefix $\restrict{x}{n}$ lies in
    $\ClosedTreeCode{F}$.
    If $x\notin F$, closedness of $F$ makes $\SetDifference{\BaireSpace}{F}$ open, so some cylinder $\cyl{\restrict{x}{n}}$
    is
    contained in $\SetDifference{\BaireSpace}{F}$; hence $\restrict{x}{n}\notin\ClosedTreeCode{F}$ and
    $x\notin\TreeBody{\ClosedTreeCode{F}}$.

    Conversely, if $T$ is a pruned subtree, then
    $$
    \SetDifference{\BaireSpace}{\TreeBody{T}}
    =
    \bigcup\{\cyl{s}:s\notin T\},
    $$
    so $\TreeBody{T}$ is closed.
    Finally, $\ClosedTreeCode{\TreeBody{T}}=T$.
    If $s\in T$, prunedness gives some $x\in\TreeBody{T}\cap\cyl{s}$.
    If $s\notin T$, then no point of $\cyl{s}$ lies in $\TreeBody{T}$.
    This proves that the two assignments are inverse.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    Cantor space $\CantorSpace$ is the binary version of the same tree picture. Its full prefix tree is
    $(\finseq{2},\prefixOf)$, and a subtree $T\IncludedIn\finseq{2}$ has body
    $$
    \TreeBody{T}:=\{x\in\CantorSpace:\restrict{x}{n}\in T\text{ for every }n\in\omega\}.
    $$
    Exactly as above, closed subsets of $\CantorSpace$ are the bodies of pruned binary trees.
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: claim
  excerpt: |
    $\ClosedSets{\BaireSpace}$ is in one-to-one correspondence with the pruned elements of $\PrefixSubtrees{\omega}$, via $T\mapsto\TreeBody{T}$ and $F\mapsto \ClosedTreeCode{F}:=\{s\in\finseq{\omega}:\cyl{s}\cap F\ne\emptyset\}$. \end{claim*}
-/
theorem closed_sets_pruned_subtrees_correspond [TopologicalSpace A] [DiscreteTopology A]
    (F : Set (ℕ → A)) :
    IsClosed F ↔ ∃ T : Set (finseq A),
      IsSubtree T ∧ IsPruned T ∧ F = treeBody T := by
  constructor
  · intro hF
    exact ⟨closedTreeCode F, closedTreeCode_isSubtree F, closedTreeCode_isPruned F,
      (treeBody_closedTreeCode_eq_of_closed hF).symm⟩
  · rintro ⟨T, _, _, rfl⟩
    exact isClosed_treeBody T

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    For example, intersections become intersections of trees:
    $$
    \TreeBody{S}\cap\TreeBody{T}
    =
    \TreeBody{S\cap T}.
    $$
-/
theorem treeBody_inter (S T : Set (finseq A)) :
    treeBody S ∩ treeBody T = treeBody (S ∩ T) := by
  ext x
  constructor
  · rintro ⟨hxS, hxT⟩ n
    exact ⟨hxS n, hxT n⟩
  · intro hx
    exact ⟨fun n => (hx n).1, fun n => (hx n).2⟩

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The pruned subtree corresponding to $\TreeBody{S}\cap\TreeBody{T}$ under the bijection is
    $\ClosedTreeCode{\TreeBody{S\cap T}}$.
-/
theorem prunedRepresentative_treeBody_inter [TopologicalSpace A] [DiscreteTopology A]
    (S T : Set (finseq A)) :
    IsPruned (closedTreeCode (treeBody (S ∩ T))) ∧
      treeBody (closedTreeCode (treeBody (S ∩ T))) = treeBody S ∩ treeBody T := by
  refine ⟨closedTreeCode_isPruned _, ?_⟩
  rw [treeBody_closedTreeCode_eq_of_closed (isClosed_treeBody (S ∩ T)), treeBody_inter]

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The finite branching adds compactness. $\CantorSpace$ is compact by Tychonoff's theorem, since it is a product of
    compact finite discrete spaces, and it is \termuseas{perfect space}{perfect} because every binary cylinder has the two
    proper subcylinders $\cyl{s\concat(0)}$ and $\cyl{s\concat(1)}$.
-/
theorem cantor_space_compact_recall :
    CompactSpace cantor_space :=
  cantor_space_compact

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: lemma
  title: Lemma (König)
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Since $\TreeBody{T}=\emptyset$,
    $$
    \CantorSpace=\bigcup\{\cyl{s}:s\notin T\}.
    $$
    Compactness gives a finite subcover by cylinders $\cyl{s_0},\ldots,\cyl{s_{m-1}}$ with each $s_i\notin T$.
    Let $N=\max_i |s_i|$. If some $t\in T$ had length $N$, choose any branch $x\in\cyl{t}$.
    The finite subcover puts $x$ in some $\cyl{s_i}$.
    Since $|s_i|\le N$, this means $s_i\prefixOf t$, contradicting downward closure of $T$.
    \end{proof}
-/
theorem konig_binary_tree_bounded_of_empty_body {T : Set (finseq Bool)}
    (hT : IsSubtree T) (hempty : treeBody T = ∅) :
    ∃ n : ℕ, ∀ s : finseq Bool, s.length = n → s ∉ T := by
  have : CompactSpace cantor_space := cantor_space_compact
  have hcover :
      (Set.univ : Set cantor_space) ⊆ ⋃ s : {s : finseq Bool // s ∉ T}, cyl s.1 := by
    intro x _
    have hx : x ∈ (treeBody T)ᶜ := by simp [hempty]
    simpa [compl_treeBody_eq_cylinderCode_compl, cylinderCode] using hx
  obtain ⟨F, hF⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun s : {s : finseq Bool // s ∉ T} => cyl s.1)
      (fun s => isOpen_cyl s.1) hcover
  let N : ℕ := F.sup fun s : {s : finseq Bool // s ∉ T} => s.1.length
  refine ⟨N, ?_⟩
  intro u huN huT
  let x : ℕ → Bool := extendFinseq u
  have hxcover : x ∈ ⋃ s ∈ F, cyl s.1 := hF (Set.mem_univ x)
  rcases Set.mem_iUnion.1 hxcover with ⟨s, hxcover⟩
  rcases Set.mem_iUnion.1 hxcover with ⟨hsF, hxs⟩
  have hslen : s.1.length ≤ u.length := by
    rw [huN]
    exact Finset.le_sup
      (s := F) (f := fun s : {s : finseq Bool // s ∉ T} => s.1.length) hsF
  have hprefix : prefixOf s.1 u := by
    change s.1 <+: u
    rw [List.prefix_iff_getElem]
    refine ⟨hslen, ?_⟩
    intro i hi
    have hiu : i < u.length := lt_of_lt_of_le hi hslen
    calc
      s.1[i] = x i := (hxs i hi).symm
      _ = u[i] := by simp [x, extendFinseq, hiu]
  exact s.2 (hT huT hprefix)

theorem cantor_cyl_false_strict_subset (s : finseq Bool) :
    cyl (concat s [false]) ⊂ cyl s := by
  have hsub : cyl (concat s [false]) ⊆ cyl s := cyl_concat_subset s [false]
  rw [ssubset_def]
  refine ⟨hsub, ?_⟩
  intro hrev
  have hp : prefixOf (concat s [false]) s := (cyl_subset_iff_prefix (A := Bool)).1 hrev
  have hlen := hp.length_le
  simp [concat] at hlen

theorem cantor_cyl_true_strict_subset (s : finseq Bool) :
    cyl (concat s [true]) ⊂ cyl s := by
  have hsub : cyl (concat s [true]) ⊆ cyl s := cyl_concat_subset s [true]
  rw [ssubset_def]
  refine ⟨hsub, ?_⟩
  intro hrev
  have hp : prefixOf (concat s [true]) s := (cyl_subset_iff_prefix (A := Bool)).1 hrev
  have hlen := hp.length_le
  simp [concat] at hlen

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    By compactness, or equivalently by this finite-branching König bound, clopen subsets of $\CantorSpace$ are finite
    unions of binary cylinders.
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The Cantor space $\CantorSpace$ admits the same cylinder/tree picture, with two compactness-driven simplifications.
    Trees range over $\finseq{2}$ instead of $\finseq{\omega}$, so closed sets are bodies $\TreeBody{T}$ of pruned *binary*
    trees. And because $\CantorSpace$ is itself compact, every closed subset is compact, every open cover of a clopen set by
    cylinders has a finite subcover, and so every clopen set is a *finite* union of cylinders — equivalently, decided by
    reading a single bounded prefix length.
-/
theorem cantor_clopen_eq_finite_iUnion_cyl {U : Set cantor_space} (hU : IsClopen U) :
    ∃ F : Finset {s : finseq Bool // cyl s ⊆ U}, U = ⋃ s ∈ F, cyl s.1 := by
  have : CompactSpace cantor_space := cantor_space_compact
  have hcover : U ⊆ ⋃ s : {s : finseq Bool // cyl s ⊆ U}, cyl s.1 := by
    rw [← isOpen_eq_iUnion_cyl (A := Bool) hU.isOpen]
  obtain ⟨F, hF⟩ :=
    hU.isClosed.isCompact.elim_finite_subcover
      (fun s : {s : finseq Bool // cyl s ⊆ U} => cyl s.1)
      (fun s => isOpen_cyl s.1) hcover
  refine ⟨F, Set.Subset.antisymm hF ?_⟩
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨s, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨_, hxs⟩
  exact s.2 hxs

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    Even when $S$ and $T$ are pruned, $S\cap T$ may not be.
    For example, let
    $$
    S=\{\wordRepeat{0}{n}:n\in\omega\},
    \qquad
    T=\{\wordRepeat{1}{n}:n\in\omega\}.
    $$
    Both are pruned, witnessed by the constant branches $0^\omega$ and $1^\omega$, respectively.
    But $S\cap T=\{\emptySeq\}$, whose body is empty, so the root has no branch through $S\cap T$.
-/
def falseRayTree : Set (finseq Bool) :=
  {s | prefixOfSeq s fun _ => false}

def trueRayTree : Set (finseq Bool) :=
  {s | prefixOfSeq s fun _ => true}

theorem falseRayTree_isSubtree :
    IsSubtree falseRayTree := by
  intro s t ht hst
  exact prefixOfSeq_of_prefix hst ht

theorem trueRayTree_isSubtree :
    IsSubtree trueRayTree := by
  intro s t ht hst
  exact prefixOfSeq_of_prefix hst ht

theorem falseRayTree_isPruned :
    IsPruned falseRayTree := by
  intro s hs
  refine ⟨fun _ => false, ?_, hs⟩
  intro n
  exact prefixOfSeq_seqPrefix (fun _ : ℕ => false) n

theorem trueRayTree_isPruned :
    IsPruned trueRayTree := by
  intro s hs
  refine ⟨fun _ => true, ?_, hs⟩
  intro n
  exact prefixOfSeq_seqPrefix (fun _ : ℕ => true) n

theorem falseRayTree_inter_trueRayTree_not_pruned :
    ¬ IsPruned (falseRayTree ∩ trueRayTree) := by
  intro hpruned
  have hnil : ([] : finseq Bool) ∈ falseRayTree ∩ trueRayTree := by
    exact ⟨prefixOfSeq_nil _, prefixOfSeq_nil _⟩
  rcases hpruned hnil with ⟨x, hxbody, _⟩
  have hfalse : prefixOfSeq (seqPrefix x 1) (fun _ : ℕ => false) := (hxbody 1).1
  have htrue : prefixOfSeq (seqPrefix x 1) (fun _ : ℕ => true) := (hxbody 1).2
  have hxfalse : false = x 0 := by
    simpa [seqPrefix] using hfalse 0 (by simp [seqPrefix])
  have hxtrue : true = x 0 := by
    simpa [seqPrefix] using htrue 0 (by simp [seqPrefix])
  exact Bool.false_ne_true (hxfalse.trans hxtrue.symm)

/-!
## Baire-space coding consequences

This records the local formal content used after the tree-coding section:
open information is finite-prefix information, and closed subsets are exactly
bodies of pruned countable prefix trees. The Cauchy-name surjection onto
arbitrary Polish spaces is handled in the representation chapter.
-/

theorem baire_open_neighborhood_contains_cylinder {U : Set baire_space} {x : baire_space}
    (hx : x ∈ U) (hU : IsOpen U) :
    ∃ s : finseq ℕ, x ∈ cyl s ∧ cyl s ⊆ U :=
  exists_cyl_subset_of_mem_open (A := ℕ) hx hU

theorem baire_closed_iff_exists_pruned_tree_body (F : Set baire_space) :
    IsClosed F ↔ ∃ T : Set (finseq ℕ), IsSubtree T ∧ IsPruned T ∧ F = treeBody T :=
  closed_sets_pruned_subtrees_correspond F

end CylinderCodesPrefixTrees

/-- Book phrase "no point has a compact neighborhood." -/
def NoCompactNeighborhoods (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ¬ ∃ K : Set Y, IsCompact K ∧ K ∈ 𝓝 y

theorem noCompactNeighborhoods_open_subtype {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : IsOpen s) (hX : NoCompactNeighborhoods X) :
    NoCompactNeighborhoods s := by
  intro x hcompact
  rcases hcompact with ⟨K, hK_compact, hK_nhds⟩
  have hK_image_compact : IsCompact (((↑) : s → X) '' K) :=
    hK_compact.image continuous_subtype_val
  have hK_image_nhdsWithin : (((↑) : s → X) '' K) ∈ 𝓝[s] (x : X) :=
    (mem_nhds_subtype_iff_nhdsWithin (s := s) (a := x) (t := K)).mp hK_nhds
  have hK_image_nhds : (((↑) : s → X) '' K) ∈ 𝓝 (x : X) := by
    simpa [hs.nhdsWithin_eq x.2] using hK_image_nhdsWithin
  exact hX (x : X) ⟨_, hK_image_compact, hK_image_nhds⟩

theorem not_isCompact_of_nonempty_open_of_noCompactNeighborhoods {X : Type u}
    [TopologicalSpace X] {U : Set X} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hX : NoCompactNeighborhoods X) :
    ¬ IsCompact U := by
  intro hU_compact
  rcases hU_nonempty with ⟨x, hxU⟩
  exact hX x ⟨U, hU_compact, hU_open.mem_nhds hxU⟩

section SubspaceClassificationProperties

variable {X : Type u} [TopologicalSpace X]

theorem zeroDimensional_subtype (s : Set X) (hX : IsZeroDimensional X) :
    IsZeroDimensional s := by
  have hb := isTopologicalBasis_subtype hX (fun x => x ∈ s)
  exact hb.of_isOpen_of_subset (s' := {U : Set s | IsClopen U})
    (fun U hU => hU.isOpen)
    (by
      rintro U ⟨V, hV, rfl⟩
      exact hV.preimage continuous_subtype_val)

theorem perfectSpace_open_subtype {s : Set X} (hs : IsOpen s) [PerfectSpace X] :
    PerfectSpace s := by
  refine ⟨?_⟩
  rw [preperfect_iff_nhds]
  intro x _ U hU
  rcases (mem_nhds_subtype s x U).mp hU with ⟨V, hV, hVU⟩
  have hs_preperfect : Preperfect s := hs.preperfect
  rcases (preperfect_iff_nhds.mp hs_preperfect (x : X) x.2 V hV) with
    ⟨y, hyVs, hy_ne⟩
  refine ⟨⟨y, hyVs.2⟩, ⟨hVU hyVs.1, mem_univ _⟩, ?_⟩
  intro hxy
  exact hy_ne (congrArg Subtype.val hxy)

theorem open_subspace_alexandrov_urysohn_hypotheses {s : Set X}
    (hs : IsOpen s) [PerfectSpace X] (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) :
    PerfectSpace s ∧ IsZeroDimensional s ∧ NoCompactNeighborhoods s := by
  exact ⟨perfectSpace_open_subtype hs, zeroDimensional_subtype s hzero,
    noCompactNeighborhoods_open_subtype hs hnlc⟩

theorem not_totallyBounded_of_nonempty_clopen_of_noCompactNeighborhoods
    {X : Type u} [MetricSpace X] (hcomplete : IsMetricComplete X)
    (hnlc : NoCompactNeighborhoods X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) :
    ¬ TotallyBounded U := by
  intro hU_totallyBounded
  have : CompleteSpace X := (isMetricComplete_iff_completeSpace X).1 hcomplete
  have hU_compact : IsCompact U :=
    hU_totallyBounded.isCompact_of_isClosed hU.isClosed
  exact not_isCompact_of_nonempty_open_of_noCompactNeighborhoods
    hU.isOpen hU_nonempty hnlc hU_compact

theorem exists_positive_no_finite_diameter_cover_of_nonempty_clopen
    {X : Type u} [MetricSpace X] (hcomplete : IsMetricComplete X)
    (hnlc : NoCompactNeighborhoods X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ F : Finset {V : Set X //
          V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε},
        ¬ U ⊆ ⋃ V ∈ F, V.1 := by
  classical
  have hU_not_totallyBounded :
      ¬ TotallyBounded U :=
    not_totallyBounded_of_nonempty_clopen_of_noCompactNeighborhoods
      hcomplete hnlc hU hU_nonempty
  rw [Metric.totallyBounded_iff] at hU_not_totallyBounded
  push Not at hU_not_totallyBounded
  rcases hU_not_totallyBounded with ⟨r, hr_pos, hno_ball_cover⟩
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro F hF_cover
  let center :
      {V : Set X // V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ r / 2} → X :=
    fun V => if hV : V.1.Nonempty then Classical.choose hV else Classical.choose hU_nonempty
  let C : Set X := center '' (F : Set {V : Set X //
      V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ r / 2})
  have hC_finite : C.Finite := F.finite_toSet.image center
  have hball_cover : U ⊆ ⋃ y ∈ C, Metric.ball y r := by
    intro x hxU
    have hxF := hF_cover hxU
    rcases Set.mem_iUnion.1 hxF with ⟨V, hxF'⟩
    rcases Set.mem_iUnion.1 hxF' with ⟨hVF, hxV⟩
    have hV_nonempty : V.1.Nonempty := ⟨x, hxV⟩
    have hcenter_mem : center V ∈ V.1 := by
      dsimp [center]
      rw [dite_eq_left hV_nonempty]
      exact Classical.choose_spec hV_nonempty
    have hdist_le : dist x (center V) ≤ r / 2 :=
      V.2.2 x hxV (center V) hcenter_mem
    have hdist_lt : dist x (center V) < r := by
      exact lt_of_le_of_lt hdist_le (half_lt_self hr_pos)
    exact Set.mem_iUnion.2 ⟨center V, Set.mem_iUnion.2 ⟨⟨V, hVF, rfl⟩, hdist_lt⟩⟩
  exact hno_ball_cover C hC_finite hball_cover

theorem exists_countable_clopen_cover_small_of_open
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU_open : IsOpen U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ → {V : Set X //
        IsClopen V ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε},
      U ⊆ ⋃ n : ℕ, (B n).1 := by
  let SmallClopen : Type u := {V : Set X //
    IsClopen V ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}
  let emptySmall : SmallClopen :=
    ⟨∅, isClopen_empty, by simp, by simp⟩
  have : Nonempty SmallClopen := ⟨emptySmall⟩
  have hcover : U ⊆ ⋃ V : SmallClopen, V.1 := by
    intro x hxU
    let O : Set X := U ∩ Metric.ball x (ε / 2)
    have hO_open : IsOpen O :=
      hU_open.inter Metric.isOpen_ball
    have hxO : x ∈ O :=
      ⟨hxU, Metric.mem_ball_self (half_pos hε)⟩
    obtain ⟨V, hV_clopen, hxV, hVU⟩ := hzero.exists_subset_of_mem_open hxO hO_open
    have hV_sub_U : V ⊆ U := fun y hy => (hVU hy).1
    have hV_small : ∀ y ∈ V, ∀ z ∈ V, dist y z ≤ ε := by
      intro y hy z hz
      have hy_ball : y ∈ Metric.ball x (ε / 2) := (hVU hy).2
      have hz_ball : z ∈ Metric.ball x (ε / 2) := (hVU hz).2
      have hy_dist : dist y x < ε / 2 := by simpa [Metric.mem_ball] using hy_ball
      have hz_dist : dist z x < ε / 2 := by simpa [Metric.mem_ball] using hz_ball
      have hlt : dist y z < ε := by
        calc
          dist y z ≤ dist y x + dist z x := dist_triangle_right y z x
          _ < ε / 2 + ε / 2 := add_lt_add hy_dist hz_dist
          _ = ε := by ring
      exact hlt.le
    exact Set.mem_iUnion.2 ⟨⟨V, hV_clopen, hV_sub_U, hV_small⟩, hxV⟩
  exact (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover
    (fun V : SmallClopen => V.1) (fun V => V.2.1.isOpen) hcover

theorem isClopen_finset_biUnion {X : Type u} [TopologicalSpace X]
    {ι : Type*} (F : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ F, IsClopen (A i)) :
    IsClopen (⋃ i ∈ F, A i) := by
  classical
  revert hA
  refine Finset.induction_on F ?_ ?_
  · intro _hA
    simpa using (isClopen_empty : IsClopen (∅ : Set X))
  · intro a F haF ih hA
    have ha : IsClopen (A a) := hA a (by simp)
    have hF : IsClopen (⋃ i ∈ F, A i) := ih fun i hi => hA i (by simp [hi])
    simpa [haF] using ha.union hF

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    Let $\mathcal U$ be any open cover. Enumerate the members of this clopen base that are contained in some member of
    $\mathcal U$ as $C_0,C_1,\ldots$, allowing repetitions if the family is finite. They cover $X$. Put
    $$D_n:=\SetDifference{C_n}{\bigcup_{j<n}C_j}.$$
    The sets $D_n$ are clopen, pairwise disjoint, and cover $X$: each point $x$ belongs to $D_n$ for the
    least $n$ with $x\in C_n$. Moreover, each $D_n$ lies in some member of $\mathcal U$.
-/
def disjointSeq (A : ℕ → Set X) (n : ℕ) : Set X :=
  A n \ ⋃ k ∈ Finset.range n, A k

omit [TopologicalSpace X] in
theorem disjointSeq_subset (A : ℕ → Set X) (n : ℕ) :
    disjointSeq A n ⊆ A n :=
  fun _ hx => hx.1

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    Let $\mathcal U$ be any open cover. Enumerate the members of this clopen base that are contained in some member of
    $\mathcal U$ as $C_0,C_1,\ldots$, allowing repetitions if the family is finite. They cover $X$. Put
    $$D_n:=\SetDifference{C_n}{\bigcup_{j<n}C_j}.$$
    The sets $D_n$ are clopen, pairwise disjoint, and cover $X$: each point $x$ belongs to $D_n$ for the
    least $n$ with $x\in C_n$. Moreover, each $D_n$ lies in some member of $\mathcal U$.
-/
theorem disjointSeq_isClopen {A : ℕ → Set X}
    (hA : ∀ n, IsClopen (A n)) (n : ℕ) :
    IsClopen (disjointSeq A n) := by
  have hprev : IsClopen (⋃ k ∈ Finset.range n, A k) :=
    isClopen_finset_biUnion (Finset.range n) A fun k _hk => hA k
  exact (hA n).diff hprev

omit [TopologicalSpace X] in
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    Let $\mathcal U$ be any open cover. Enumerate the members of this clopen base that are contained in some member of
    $\mathcal U$ as $C_0,C_1,\ldots$, allowing repetitions if the family is finite. They cover $X$. Put
    $$D_n:=\SetDifference{C_n}{\bigcup_{j<n}C_j}.$$
    The sets $D_n$ are clopen, pairwise disjoint, and cover $X$: each point $x$ belongs to $D_n$ for the
    least $n$ with $x\in C_n$. Moreover, each $D_n$ lies in some member of $\mathcal U$.
-/
theorem iUnion_disjointSeq_eq_iUnion (A : ℕ → Set X) :
    (⋃ n : ℕ, disjointSeq A n) = ⋃ n : ℕ, A n := by
  classical
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
    exact Set.mem_iUnion.2 ⟨n, hxn.1⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨_n, _hxn⟩
    have hexists : ∃ n : ℕ, x ∈ A n := by simpa using hx
    let n : ℕ := Nat.find hexists
    have hn : x ∈ A n := Nat.find_spec hexists
    have hnot_prev : x ∉ ⋃ k ∈ Finset.range n, A k := by
      intro hxprev
      rcases Set.mem_iUnion.1 hxprev with ⟨k, hxprev'⟩
      rcases Set.mem_iUnion.1 hxprev' with ⟨hk, hxk⟩
      exact Nat.find_min hexists (Finset.mem_range.mp hk) hxk
    exact Set.mem_iUnion.2 ⟨n, hn, hnot_prev⟩

omit [TopologicalSpace X] in
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    Let $\mathcal U$ be any open cover. Enumerate the members of this clopen base that are contained in some member of
    $\mathcal U$ as $C_0,C_1,\ldots$, allowing repetitions if the family is finite. They cover $X$. Put
    $$D_n:=\SetDifference{C_n}{\bigcup_{j<n}C_j}.$$
    The sets $D_n$ are clopen, pairwise disjoint, and cover $X$: each point $x$ belongs to $D_n$ for the
    least $n$ with $x\in C_n$. Moreover, each $D_n$ lies in some member of $\mathcal U$.
-/
theorem disjointSeq_pairwiseDisjoint (A : ℕ → Set X) :
    Pairwise fun m n => Disjoint (disjointSeq A m) (disjointSeq A n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro x hxm hxn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hxn.2 (Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hlt, hxm.1⟩⟩)
  · exact hxm.2 (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hgt, hxn.1⟩⟩)

omit [TopologicalSpace X] in
theorem disjointSeq_small_of_small [PseudoMetricSpace X] {A : ℕ → Set X} {ε : ℝ}
    (hsmall : ∀ n, ∀ x ∈ A n, ∀ y ∈ A n, dist x y ≤ ε) (n : ℕ) :
    ∀ x ∈ disjointSeq A n, ∀ y ∈ disjointSeq A n, dist x y ≤ ε := by
  intro x hx y hy
  exact hsmall n x hx.1 y hy.1

theorem exists_countable_disjoint_clopen_cover_small_of_open
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU_open : IsOpen U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : ℕ → Set X,
      (∀ n : ℕ,
        IsClopen (W n) ∧ W n ⊆ U ∧
          ∀ x ∈ W n, ∀ y ∈ W n, dist x y ≤ ε) ∧
        Pairwise (fun m n => Disjoint (W m) (W n)) ∧
          U ⊆ ⋃ n : ℕ, W n := by
  obtain ⟨B, hB_cover⟩ :=
    exists_countable_clopen_cover_small_of_open (X := X) hzero hU_open hε
  let A : ℕ → Set X := fun n => (B n).1
  refine ⟨disjointSeq A, ?_, disjointSeq_pairwiseDisjoint A, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · exact disjointSeq_isClopen (A := A) (fun n => (B n).2.1) n
    · exact (disjointSeq_subset A n).trans (B n).2.2.1
    · exact disjointSeq_small_of_small
        (A := A) (ε := ε) (fun n => (B n).2.2.2) n
  · intro x hxU
    have hxA : x ∈ ⋃ n : ℕ, A n := hB_cover hxU
    simpa [A, iUnion_disjointSeq_eq_iUnion] using hxA

theorem exists_countable_disjoint_clopen_cover_small_of_noncompact_clopen
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : ℕ → Set X,
      (∀ n : ℕ,
        IsClopen (W n) ∧ W n ⊆ U ∧
          ∀ x ∈ W n, ∀ y ∈ W n, dist x y ≤ ε) ∧
        Pairwise (fun m n => Disjoint (W m) (W n)) ∧
          U ⊆ ⋃ n : ℕ, W n ∧
            ∀ S : Finset ℕ, ∃ n : ℕ, n ∉ S ∧ (W n).Nonempty := by
  classical
  obtain ⟨ε, hε_pos, hno_finite_cover⟩ :=
    exists_positive_no_finite_diameter_cover_of_nonempty_clopen
      hcomplete hnlc hU hU_nonempty
  obtain ⟨W, hW_props, hW_disjoint, hW_cover⟩ :=
    exists_countable_disjoint_clopen_cover_small_of_open (X := X) hzero hU.isOpen hε_pos
  refine ⟨ε, hε_pos, W, hW_props, hW_disjoint, hW_cover, ?_⟩
  intro S
  by_contra hnone
  let toPart : {n : ℕ // n ∈ S} →
      {V : Set X // V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε} :=
    fun n => ⟨W n.1, (hW_props n.1).2.1, (hW_props n.1).2.2⟩
  let F : Finset {V : Set X // V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε} :=
    S.attach.image toPart
  have hF_cover : U ⊆ ⋃ V ∈ F, V.1 := by
    intro x hxU
    rcases Set.mem_iUnion.1 (hW_cover hxU) with ⟨n, hxWn⟩
    have hnS : n ∈ S := by
      by_contra hnS
      exact hnone ⟨n, hnS, ⟨x, hxWn⟩⟩
    let nS : {n : ℕ // n ∈ S} := ⟨n, hnS⟩
    have hmemF : toPart nS ∈ F := by
      exact Finset.mem_image.2 ⟨nS, by simp [nS], rfl⟩
    exact Set.mem_iUnion.2 ⟨toPart nS, Set.mem_iUnion.2 ⟨hmemF, hxWn⟩⟩
  exact hno_finite_cover F hF_cover

omit [TopologicalSpace X] in
theorem infinite_nonempty_indices_of_arbitrarily_many
    {W : ℕ → Set X}
    (hmany : ∀ S : Finset ℕ, ∃ n : ℕ, n ∉ S ∧ (W n).Nonempty) :
    ({n : ℕ | (W n).Nonempty} : Set ℕ).Infinite := by
  classical
  by_contra hnot
  have hfinite : ({n : ℕ | (W n).Nonempty} : Set ℕ).Finite :=
    Set.not_infinite.mp hnot
  obtain ⟨n, hn_not_mem, hn_nonempty⟩ := hmany hfinite.toFinset
  exact hn_not_mem ((Set.Finite.mem_toFinset hfinite).2 hn_nonempty)

theorem exists_nat_nonempty_disjoint_clopen_cover_small_of_noncompact_clopen
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : ℕ → Set X,
      (∀ n : ℕ,
        IsClopen (V n) ∧ (V n).Nonempty ∧ V n ⊆ U ∧
          ∀ x ∈ V n, ∀ y ∈ V n, dist x y ≤ ε) ∧
        Pairwise (fun m n => Disjoint (V m) (V n)) ∧
          U = ⋃ n : ℕ, V n := by
  classical
  obtain ⟨ε, hε_pos, W, hW_props, hW_disjoint, hW_cover, hmany⟩ :=
    exists_countable_disjoint_clopen_cover_small_of_noncompact_clopen
      hcomplete hzero hnlc hU hU_nonempty
  let I : Type := {n : ℕ // (W n).Nonempty}
  have hI_infinite : Infinite I := by
    exact Set.Infinite.to_subtype (infinite_nonempty_indices_of_arbitrarily_many hmany)
  let : Infinite I := hI_infinite
  let : Denumerable I := Classical.choice (nonempty_denumerable I)
  let e : ℕ → I := (Denumerable.eqv I).symm
  let V : ℕ → Set X := fun n => W (e n).1
  refine ⟨ε, hε_pos, V, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hW_props (e n).1).1, (e n).2, (hW_props (e n).1).2.1,
      (hW_props (e n).1).2.2⟩
  · intro m n hmn
    have hemn : e m ≠ e n := by
      intro h
      exact hmn ((Denumerable.eqv I).symm.injective h)
    have hval_ne : (e m).1 ≠ (e n).1 := by
      intro hval
      exact hemn (Subtype.ext hval)
    exact hW_disjoint hval_ne
  · apply Set.Subset.antisymm
    · intro x hxU
      rcases Set.mem_iUnion.1 (hW_cover hxU) with ⟨k, hxWk⟩
      let i : I := ⟨k, ⟨x, hxWk⟩⟩
      rcases (Denumerable.eqv I).symm.surjective i with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, by simpa [V, e, hn] using hxWk⟩
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hxVn⟩
      exact (hW_props (e n).1).2.1 hxVn

theorem exists_nat_nonempty_disjoint_clopen_cover_diameter_le
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : ℕ → Set X,
      (∀ n : ℕ,
        IsClopen (V n) ∧ (V n).Nonempty ∧ V n ⊆ U ∧
          ∀ x ∈ V n, ∀ y ∈ V n, dist x y ≤ δ) ∧
        Pairwise (fun m n => Disjoint (V m) (V n)) ∧
          U = ⋃ n : ℕ, V n := by
  classical
  obtain ⟨ε, hε_pos, hno_finite_cover⟩ :=
    exists_positive_no_finite_diameter_cover_of_nonempty_clopen
      hcomplete hnlc hU hU_nonempty
  let η : ℝ := min δ ε
  have hη_pos : 0 < η := lt_min hδ hε_pos
  obtain ⟨W, hW_props, hW_disjoint, hW_cover⟩ :=
    exists_countable_disjoint_clopen_cover_small_of_open (X := X) hzero hU.isOpen hη_pos
  have hmany : ∀ S : Finset ℕ, ∃ n : ℕ, n ∉ S ∧ (W n).Nonempty := by
    intro S
    by_contra hnone
    let toPart : {n : ℕ // n ∈ S} →
        {V : Set X // V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε} :=
      fun n => ⟨W n.1, (hW_props n.1).2.1, by
        intro x hx y hy
        exact ((hW_props n.1).2.2 x hx y hy).trans (min_le_right δ ε)⟩
    let F : Finset {V : Set X // V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε} :=
      S.attach.image toPart
    have hF_cover : U ⊆ ⋃ V ∈ F, V.1 := by
      intro x hxU
      rcases Set.mem_iUnion.1 (hW_cover hxU) with ⟨n, hxWn⟩
      have hnS : n ∈ S := by
        by_contra hnS
        exact hnone ⟨n, hnS, ⟨x, hxWn⟩⟩
      let nS : {n : ℕ // n ∈ S} := ⟨n, hnS⟩
      have hmemF : toPart nS ∈ F := by
        exact Finset.mem_image.2 ⟨nS, by simp [nS], rfl⟩
      exact Set.mem_iUnion.2 ⟨toPart nS, Set.mem_iUnion.2 ⟨hmemF, hxWn⟩⟩
    exact hno_finite_cover F hF_cover
  let I : Type := {n : ℕ // (W n).Nonempty}
  have hI_infinite : Infinite I := by
    exact Set.Infinite.to_subtype (infinite_nonempty_indices_of_arbitrarily_many hmany)
  let : Infinite I := hI_infinite
  let : Denumerable I := Classical.choice (nonempty_denumerable I)
  let e : ℕ → I := (Denumerable.eqv I).symm
  let V : ℕ → Set X := fun n => W (e n).1
  refine ⟨V, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(hW_props (e n).1).1, (e n).2, (hW_props (e n).1).2.1, ?_⟩
    intro x hx y hy
    exact ((hW_props (e n).1).2.2 x hx y hy).trans (min_le_left δ ε)
  · intro m n hmn
    have hemn : e m ≠ e n := by
      intro h
      exact hmn ((Denumerable.eqv I).symm.injective h)
    have hval_ne : (e m).1 ≠ (e n).1 := by
      intro hval
      exact hemn (Subtype.ext hval)
    exact hW_disjoint hval_ne
  · apply Set.Subset.antisymm
    · intro x hxU
      rcases Set.mem_iUnion.1 (hW_cover hxU) with ⟨k, hxWk⟩
      let i : I := ⟨k, ⟨x, hxWk⟩⟩
      rcases (Denumerable.eqv I).symm.surjective i with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, by simpa [V, e, hn] using hxWk⟩
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hxVn⟩
      exact (hW_props (e n).1).2.1 hxVn

theorem exists_baire_successor_partition
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) (n : ℕ) :
    ∃ V : ℕ → Set X,
      (∀ i, IsClopen (V i)) ∧
      (∀ i, (V i).Nonempty) ∧
      (∀ i, V i ⊆ U) ∧
      (∀ i, ∀ x ∈ V i, ∀ y ∈ V i, dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      U = ⋃ i, V i ∧
      Pairwise fun i j => Disjoint (V i) (V j) := by
  obtain ⟨V, hV, hV_disjoint, hV_cover⟩ :=
    exists_nat_nonempty_disjoint_clopen_cover_diameter_le
    (X := X) hcomplete hzero hnlc hU hU_nonempty
    (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1))
  exact ⟨V, fun i => (hV i).1, fun i => (hV i).2.1, fun i => (hV i).2.2.1,
    fun i => (hV i).2.2.2, hV_cover, hV_disjoint⟩

theorem exists_finite_clopen_cover_small_of_compact {X : Type u} [MetricSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU_open : IsOpen U)
    (hU_compact : IsCompact U) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset {V : Set X //
        IsClopen V ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε},
      U ⊆ ⋃ V ∈ F, V.1 := by
  let SmallClopen : Type u := {V : Set X //
    IsClopen V ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}
  have hcover : U ⊆ ⋃ V : SmallClopen, V.1 := by
    intro x hxU
    let O : Set X := U ∩ Metric.ball x (ε / 2)
    have hO_open : IsOpen O := by
      exact hU_open.inter Metric.isOpen_ball
    have hxO : x ∈ O := by
      exact ⟨hxU, Metric.mem_ball_self (half_pos hε)⟩
    obtain ⟨V, hV_clopen, hxV, hVU⟩ := hzero.exists_subset_of_mem_open hxO hO_open
    have hV_sub_U : V ⊆ U := fun y hy => (hVU hy).1
    have hV_small : ∀ y ∈ V, ∀ z ∈ V, dist y z ≤ ε := by
      intro y hy z hz
      have hy_ball : y ∈ Metric.ball x (ε / 2) := (hVU hy).2
      have hz_ball : z ∈ Metric.ball x (ε / 2) := (hVU hz).2
      have hy_dist : dist y x < ε / 2 := by simpa [Metric.mem_ball] using hy_ball
      have hz_dist : dist z x < ε / 2 := by simpa [Metric.mem_ball] using hz_ball
      have hlt : dist y z < ε := by
        calc
          dist y z ≤ dist y x + dist z x := dist_triangle_right y z x
          _ < ε / 2 + ε / 2 := add_lt_add hy_dist hz_dist
          _ = ε := by ring
      exact hlt.le
    exact Set.mem_iUnion.2 ⟨⟨V, hV_clopen, hV_sub_U, hV_small⟩, hxV⟩
  obtain ⟨F, hF⟩ :=
    hU_compact.elim_finite_subcover (fun V : SmallClopen => V.1)
      (fun V => V.2.1.isOpen) hcover
  exact ⟨F, hF⟩

theorem exists_finite_clopen_cover_small_of_compact_clopen {X : Type u} [MetricSpace X]
    [CompactSpace X] (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset {V : Set X //
        IsClopen V ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε},
      U ⊆ ⋃ V ∈ F, V.1 :=
  exists_finite_clopen_cover_small_of_compact hzero hU.isOpen hU.isClosed.isCompact hε

theorem exists_finite_nonempty_disjoint_clopen_cover_small_of_compact_clopen
    {X : Type u} [MetricSpace X] [CompactSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : Finset {V : Set X //
        IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε},
      U ⊆ ⋃ V ∈ F, V.1 ∧
        (F : Set {V : Set X //
          IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}).PairwiseDisjoint
            fun V => V.1 := by
  classical
  let SmallClopen : Type u := {V : Set X //
    IsClopen V ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}
  obtain ⟨F₀, hF₀_cover⟩ :=
    exists_finite_clopen_cover_small_of_compact_clopen (X := X) hzero hU hε
  let C : F₀ → TopologicalSpace.Clopens X := fun V => ⟨V.1.1, V.1.2.1⟩
  obtain ⟨D, hD_le, hD_sup, hD_disjoint⟩ := Fintype.exists_disjointed_le C
  let I : Finset F₀ := Finset.univ.filter fun V => D V ≠ ⊥
  let toPart : I → {V : Set X //
      IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε} := fun V =>
    ⟨(D V.1 : Set X), (D V.1).isClopen, by
      have hne : D V.1 ≠ ⊥ := (Finset.mem_filter.mp V.2).2
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      exact hne (TopologicalSpace.Clopens.ext hempty),
      by
        intro x hx
        exact V.1.1.2.2.1 (hD_le V.1 hx),
      by
        intro x hx y hy
        exact V.1.1.2.2.2 x (hD_le V.1 hx) y (hD_le V.1 hy)⟩
  let F : Finset {V : Set X //
      IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε} :=
    Finset.univ.image toPart
  refine ⟨F, ?_, ?_⟩
  · intro x hxU
    have hxC : x ∈ (Finset.univ.sup C : TopologicalSpace.Clopens X) := by
      change x ∈ ((Finset.univ.sup C : TopologicalSpace.Clopens X) : Set X)
      rw [TopologicalSpace.Clopens.coe_finset_sup]
      rcases Set.mem_iUnion₂.1 (hF₀_cover hxU) with ⟨V, hVF, hxV⟩
      exact Set.mem_iUnion₂.2 ⟨⟨V, hVF⟩, Finset.mem_univ _, by simpa [C] using hxV⟩
    have hxD : x ∈ (Finset.univ.sup D : TopologicalSpace.Clopens X) := by
      rw [hD_sup]
      exact hxC
    change x ∈ ((Finset.univ.sup D : TopologicalSpace.Clopens X) : Set X) at hxD
    rw [TopologicalSpace.Clopens.coe_finset_sup] at hxD
    rcases Set.mem_iUnion₂.1 hxD with ⟨V, _hV_univ, hxV⟩
    have hV_ne : D V ≠ ⊥ := by
      intro hbot
      have : x ∈ ((⊥ : TopologicalSpace.Clopens X) : Set X) := by
        rw [← hbot]
        exact hxV
      exact this
    let W : I := ⟨V, by simp [I, hV_ne]⟩
    have hW_mem : toPart W ∈ F := by
      exact Finset.mem_image.2 ⟨W, Finset.mem_univ W, rfl⟩
    exact Set.mem_iUnion₂.2 ⟨toPart W, hW_mem, by simpa [toPart, W] using hxV⟩
  · intro A hAF B hBF hAB
    rcases Finset.mem_image.1 hAF with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.1 hBF with ⟨j, _hj, rfl⟩
    have hij : i.1 ≠ j.1 := by
      intro hij
      exact hAB (congrArg toPart (Subtype.ext hij))
    exact TopologicalSpace.Clopens.coe_disjoint.2 (hD_disjoint hij)

theorem exists_clopen_split_of_nonempty_clopen [T1Space X] [PerfectSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) :
    ∃ V W : Set X,
      IsClopen V ∧ IsClopen W ∧ V.Nonempty ∧ W.Nonempty ∧ V ∩ W = ∅ ∧ V ∪ W = U := by
  rcases hU_nonempty with ⟨x, hxU⟩
  rcases (preperfect_iff_nhds.mp PerfectSpace.univ_preperfect x (mem_univ x) U
      (hU.isOpen.mem_nhds hxU)) with ⟨y, hyUuniv, hy_ne⟩
  have hUy : y ∈ U := hyUuniv.1
  have hO_open : IsOpen (U \ ({y} : Set X)) :=
    hU.isOpen.sdiff isClosed_singleton
  have hxO : x ∈ U \ ({y} : Set X) := by
    exact ⟨hxU, by simpa using hy_ne.symm⟩
  obtain ⟨V, hV_clopen, hxV, hVU⟩ := hzero.exists_subset_of_mem_open hxO hO_open
  let W : Set X := U \ V
  have hV_sub_U : V ⊆ U := fun z hz => (hVU hz).1
  have hy_not_V : y ∉ V := by
    intro hyV
    exact by simpa using (hVU hyV).2
  refine ⟨V, W, hV_clopen, hU.diff hV_clopen, ⟨x, hxV⟩, ⟨y, hUy, hy_not_V⟩, ?_, ?_⟩
  · ext z
    simp [W]
  · ext z
    constructor
    · rintro (hzV | hzW)
      · exact hV_sub_U hzV
      · exact hzW.1
    · intro hzU
      by_cases hzV : z ∈ V
      · exact Or.inl hzV
      · exact Or.inr ⟨hzU, hzV⟩

theorem exists_finite_two_le_nonempty_disjoint_clopen_cover_small_of_compact_clopen
    {X : Type u} [MetricSpace X] [CompactSpace X] [PerfectSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U) (hU_nonempty : U.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset {V : Set X //
        IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε},
      2 ≤ F.card ∧ U ⊆ ⋃ V ∈ F, V.1 ∧
        (F : Set {V : Set X //
          IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}).PairwiseDisjoint
            fun V => V.1 := by
  classical
  let Part : Type u := {V : Set X //
    IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}
  obtain ⟨F, hcover, hdisjoint⟩ :=
    exists_finite_nonempty_disjoint_clopen_cover_small_of_compact_clopen
      (X := X) hzero hU hε
  by_cases hcard : 2 ≤ F.card
  · exact ⟨F, hcard, hcover, hdisjoint⟩
  have hF_nonempty : F.Nonempty := by
    rcases hU_nonempty with ⟨x, hxU⟩
    rcases Set.mem_iUnion₂.1 (hcover hxU) with ⟨V, hVF, _hxV⟩
    exact ⟨V, hVF⟩
  have hcard_eq_one : F.card = 1 := by
    have hpos : 0 < F.card := Finset.card_pos.2 hF_nonempty
    omega
  rcases Finset.card_eq_one.1 hcard_eq_one with ⟨A, hF_eq⟩
  have hU_sub_A : U ⊆ A.1 := by
    intro x hxU
    simpa [hF_eq] using hcover hxU
  have hU_small : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ ε := by
    intro x hxU y hyU
    exact A.2.2.2.2 x (hU_sub_A hxU) y (hU_sub_A hyU)
  obtain ⟨V, W, hV_clopen, hW_clopen, hV_nonempty, hW_nonempty, hVW_empty, hVW_union⟩ :=
    exists_clopen_split_of_nonempty_clopen hzero hU hU_nonempty
  have hV_sub_U : V ⊆ U := by
    intro x hxV
    rw [← hVW_union]
    exact Or.inl hxV
  have hW_sub_U : W ⊆ U := by
    intro x hxW
    rw [← hVW_union]
    exact Or.inr hxW
  let P : Part := ⟨V, hV_clopen, hV_nonempty, hV_sub_U,
    fun x hx y hy => hU_small x (hV_sub_U hx) y (hV_sub_U hy)⟩
  let Q : Part := ⟨W, hW_clopen, hW_nonempty, hW_sub_U,
    fun x hx y hy => hU_small x (hW_sub_U hx) y (hW_sub_U hy)⟩
  let G : Finset Part := {P, Q}
  have hP_ne_Q : P ≠ Q := by
    intro hPQ
    have hVW : V = W := congrArg Subtype.val hPQ
    rcases hV_nonempty with ⟨x, hxV⟩
    have hx_empty : x ∈ V ∩ W := ⟨hxV, by rwa [← hVW]⟩
    rw [hVW_empty] at hx_empty
    exact hx_empty
  have hG_card : 2 ≤ G.card := by
    simpa [G] using (Finset.card_pair hP_ne_Q).ge
  have hG_cover : U ⊆ ⋃ R ∈ G, R.1 := by
    intro x hxU
    have hxVW : x ∈ V ∪ W := by
      simpa [hVW_union] using hxU
    rcases hxVW with hxV | hxW
    · exact Set.mem_iUnion₂.2 ⟨P, by simp [G], hxV⟩
    · exact Set.mem_iUnion₂.2 ⟨Q, by simp [G], hxW⟩
  have hVW_disjoint : Disjoint V W := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hVW_empty
  have hG_disjoint : (G : Set Part).PairwiseDisjoint fun R => R.1 := by
    intro R hRG S hSG hRS
    have hRG' : R = P ∨ R = Q := by
      have : R ∈ ({P, Q} : Set Part) := by simpa [G] using hRG
      simpa using this
    have hSG' : S = P ∨ S = Q := by
      have : S ∈ ({P, Q} : Set Part) := by simpa [G] using hSG
      simpa using this
    rcases hRG' with hR | hR <;> rcases hSG' with hS | hS
    · subst R
      subst S
      exact (hRS rfl).elim
    · subst R
      subst S
      exact hVW_disjoint
    · subst R
      subst S
      exact hVW_disjoint.symm
    · subst R
      subst S
      exact (hRS rfl).elim
  exact ⟨G, hG_card, hG_cover, hG_disjoint⟩

theorem exists_fin_two_le_nonempty_disjoint_clopen_cover_small_of_compact_clopen
    {X : Type u} [MetricSpace X] [CompactSpace X] [PerfectSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U) (hU_nonempty : U.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ V : Fin k → Set X,
      (∀ i, IsClopen (V i)) ∧
      (∀ i, (V i).Nonempty) ∧
      (∀ i, V i ⊆ U) ∧
      (∀ i, ∀ x ∈ V i, ∀ y ∈ V i, dist x y ≤ ε) ∧
      U = ⋃ i, V i ∧
      Pairwise fun i j => Disjoint (V i) (V j) := by
  classical
  let Part : Type u := {V : Set X //
    IsClopen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε}
  obtain ⟨F, hcard, hcover, hdisjoint⟩ :=
    exists_finite_two_le_nonempty_disjoint_clopen_cover_small_of_compact_clopen
      (X := X) hzero hU hU_nonempty hε
  let V : Fin F.card → Set X := fun i => (F.equivFin.symm i).1.1
  refine ⟨F.card, hcard, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (F.equivFin.symm i).1.2.1
  · intro i
    exact (F.equivFin.symm i).1.2.2.1
  · intro i
    exact (F.equivFin.symm i).1.2.2.2.1
  · intro i
    exact (F.equivFin.symm i).1.2.2.2.2
  · apply Set.Subset.antisymm
    · intro x hxU
      rcases Set.mem_iUnion₂.1 (hcover hxU) with ⟨A, hAF, hxA⟩
      let A' : F := ⟨A, hAF⟩
      exact Set.mem_iUnion.2 ⟨F.equivFin A', by simp [V, A'] at hxA ⊢; exact hxA⟩
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact (F.equivFin.symm i).1.2.2.2.1 hxi
  · intro i j hij
    have hij' : (F.equivFin.symm i).1 ≠ (F.equivFin.symm j).1 := by
      intro h
      have hsub : F.equivFin.symm i = F.equivFin.symm j := Subtype.ext h
      exact hij (by simpa using congrArg F.equivFin hsub)
    exact hdisjoint (F.equivFin.symm i).2 (F.equivFin.symm j).2 hij'

theorem exists_brouwer_successor_partition
    {X : Type u} [MetricSpace X] [CompactSpace X] [PerfectSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U) (hU_nonempty : U.Nonempty)
    (n : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ V : Fin k → Set X,
      (∀ i, IsClopen (V i)) ∧
      (∀ i, (V i).Nonempty) ∧
      (∀ i, V i ⊆ U) ∧
      (∀ i, ∀ x ∈ V i, ∀ y ∈ V i, dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      U = ⋃ i, V i ∧
      Pairwise fun i j => Disjoint (V i) (V j) :=
  exists_fin_two_le_nonempty_disjoint_clopen_cover_small_of_compact_clopen
    (X := X) hzero hU hU_nonempty
    (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1))

theorem exists_nat_brouwer_successor_partition
    {X : Type u} [MetricSpace X] [CompactSpace X] [PerfectSpace X]
    (hzero : IsZeroDimensional X) {U : Set X} (hU : IsClopen U) (hU_nonempty : U.Nonempty)
    (n : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ V : ℕ → Set X,
      (∀ i, i < k → IsClopen (V i)) ∧
      (∀ i, i < k → (V i).Nonempty) ∧
      (∀ i, i < k → V i ⊆ U) ∧
      (∀ i, i < k → ∀ x ∈ V i, ∀ y ∈ V i, dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      (∀ i, k ≤ i → V i = ∅) ∧
      U = ⋃ i : {i : ℕ // i < k}, V i.1 ∧
      (∀ i j : {i : ℕ // i < k}, i ≠ j → Disjoint (V i.1) (V j.1)) := by
  classical
  obtain ⟨k, hk, W, hW_clopen, hW_nonempty, hW_subset, hW_small, hW_cover, hW_disjoint⟩ :=
    exists_brouwer_successor_partition (X := X) hzero hU hU_nonempty n
  let V : ℕ → Set X := fun i => if hi : i < k then W ⟨i, hi⟩ else ∅
  refine ⟨k, hk, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simpa [V, hi] using hW_clopen ⟨i, hi⟩
  · intro i hi
    simpa [V, hi] using hW_nonempty ⟨i, hi⟩
  · intro i hi
    simpa [V, hi] using hW_subset ⟨i, hi⟩
  · intro i hi
    simpa [V, hi] using hW_small ⟨i, hi⟩
  · intro i hki
    have hi : ¬ i < k := not_lt_of_ge hki
    simp [V, hi]
  · rw [hW_cover]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨⟨i.1, i.2⟩, by simpa [V, i.2] using hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨⟨i.1, i.2⟩, by simpa [V, i.2] using hxi⟩
  · intro i j hij
    have hijFin : (⟨i.1, i.2⟩ : Fin k) ≠ ⟨j.1, j.2⟩ := by
      intro h
      exact hij (Subtype.ext (congrArg Fin.val h))
    simpa [V, i.2, j.2] using hW_disjoint hijFin

section BrouwerCompactConstruction

variable {X : Type u} [MetricSpace X] [CompactSpace X] [PerfectSpace X]

noncomputable def brouwerStepK (hzero : IsZeroDimensional X) (U : Set X) (n : ℕ) : ℕ :=
  by
    classical
    exact if h : IsClopen U ∧ U.Nonempty then
      Classical.choose (exists_nat_brouwer_successor_partition (X := X) hzero h.1 h.2 n)
    else 2

noncomputable def brouwerStepV (hzero : IsZeroDimensional X) (U : Set X) (n : ℕ) :
    ℕ → Set X :=
  by
    classical
    exact if h : IsClopen U ∧ U.Nonempty then
      Classical.choose
        (Classical.choose_spec
          (exists_nat_brouwer_successor_partition (X := X) hzero h.1 h.2 n)).2
    else fun _ => ∅

theorem brouwerStep_spec (hzero : IsZeroDimensional X) {U : Set X} {n : ℕ}
    (hU : IsClopen U) (hU_nonempty : U.Nonempty) :
    2 ≤ brouwerStepK hzero U n ∧
      (∀ i, i < brouwerStepK hzero U n → IsClopen (brouwerStepV hzero U n i)) ∧
      (∀ i, i < brouwerStepK hzero U n → (brouwerStepV hzero U n i).Nonempty) ∧
      (∀ i, i < brouwerStepK hzero U n → brouwerStepV hzero U n i ⊆ U) ∧
      (∀ i, i < brouwerStepK hzero U n →
        ∀ x ∈ brouwerStepV hzero U n i, ∀ y ∈ brouwerStepV hzero U n i,
          dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      (∀ i, brouwerStepK hzero U n ≤ i → brouwerStepV hzero U n i = ∅) ∧
      U = ⋃ i : {i : ℕ // i < brouwerStepK hzero U n}, brouwerStepV hzero U n i.1 ∧
      (∀ i j : {i : ℕ // i < brouwerStepK hzero U n}, i ≠ j →
        Disjoint (brouwerStepV hzero U n i.1) (brouwerStepV hzero U n j.1)) := by
  classical
  let e := exists_nat_brouwer_successor_partition (X := X) hzero hU hU_nonempty n
  have hgood : IsClopen U ∧ U.Nonempty := ⟨hU, hU_nonempty⟩
  have hk : 2 ≤ Classical.choose e := (Classical.choose_spec e).1
  have hV :
      (∀ i, i < Classical.choose e →
          IsClopen (Classical.choose (Classical.choose_spec e).2 i)) ∧
        (∀ i, i < Classical.choose e →
          (Classical.choose (Classical.choose_spec e).2 i).Nonempty) ∧
        (∀ i, i < Classical.choose e →
          Classical.choose (Classical.choose_spec e).2 i ⊆ U) ∧
        (∀ i, i < Classical.choose e →
          ∀ x ∈ Classical.choose (Classical.choose_spec e).2 i,
            ∀ y ∈ Classical.choose (Classical.choose_spec e).2 i,
              dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
        (∀ i, Classical.choose e ≤ i →
          Classical.choose (Classical.choose_spec e).2 i = ∅) ∧
        U = ⋃ i : {i : ℕ // i < Classical.choose e},
          Classical.choose (Classical.choose_spec e).2 i.1 ∧
        (∀ i j : {i : ℕ // i < Classical.choose e}, i ≠ j →
          Disjoint (Classical.choose (Classical.choose_spec e).2 i.1)
            (Classical.choose (Classical.choose_spec e).2 j.1)) :=
    Classical.choose_spec (Classical.choose_spec e).2
  dsimp [brouwerStepK, brouwerStepV]
  rw [dite_eq_left hgood, dite_eq_left hgood]
  exact ⟨hk, hV⟩

noncomputable def brouwerCompactU (hzero : IsZeroDimensional X) :
    finseq ℕ → Set X :=
  fun s =>
    s.reverseRecOn (motive := fun _ => Set X) Set.univ
      (fun t i Ut => brouwerStepV hzero Ut t.length i)

noncomputable def brouwerCompactK (hzero : IsZeroDimensional X) :
    finseq ℕ → ℕ :=
  fun s => brouwerStepK hzero (brouwerCompactU hzero s) s.length

@[simp]
theorem brouwerCompactU_nil (hzero : IsZeroDimensional X) :
    brouwerCompactU hzero ([] : finseq ℕ) = Set.univ := by
  simp [brouwerCompactU]

theorem brouwerCompactU_concat (hzero : IsZeroDimensional X) (s : finseq ℕ) (i : ℕ) :
    brouwerCompactU hzero (concat s [i]) =
      brouwerStepV hzero (brouwerCompactU hzero s) s.length i := by
  simp [brouwerCompactU, concat]

theorem brouwerCompactU_node_props_of_mem [Nonempty X]
    (hzero : IsZeroDimensional X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ∀ s : finseq ℕ, s ∈ boundedBranchingTree (brouwerCompactK hzero) →
      IsClopen (brouwerCompactU hzero s) ∧
        (brouwerCompactU hzero s).Nonempty ∧
          ∀ x ∈ brouwerCompactU hzero s, ∀ y ∈ brouwerCompactU hzero s,
            dist x y ≤ (1 / 2 : ℝ) ^ s.length := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
      intro _hs
      refine ⟨?_, ?_, ?_⟩
      · simpa [brouwerCompactU] using (isClopen_univ : IsClopen (Set.univ : Set X))
      · simp [brouwerCompactU,
          (show (Set.univ : Set X).Nonempty from ⟨Classical.arbitrary X, mem_univ _⟩)
        ]
      intro x _ y _
      simpa using hbounded x y
  | append_singleton t i ih =>
      intro hs
      have hsplit :
          t ∈ boundedBranchingTree (brouwerCompactK hzero) ∧
            i < brouwerCompactK hzero t := by
        simpa [concat] using
          (boundedBranchingTree_child_mem_iff (brouwerCompactK hzero) t i).1 hs
      rcases ih hsplit.1 with ⟨hclopen, hnonempty, _hdist⟩
      have hstep := brouwerStep_spec (X := X) hzero (n := t.length) hclopen hnonempty
      rcases hstep with
        ⟨_hk, hchild_clopen, hchild_nonempty, _hchild_subset, hchild_small,
          _hempty, _hcover, _hdisjoint⟩
      have hi :
          i < brouwerStepK hzero (brouwerCompactU hzero t) t.length := by
        simpa [brouwerCompactK] using hsplit.2
      refine ⟨?_, ?_, ?_⟩
      · simpa [concat, brouwerCompactU_concat] using hchild_clopen i hi
      · simpa [concat, brouwerCompactU_concat] using hchild_nonempty i hi
      · intro x hx y hy
        have hsmall :=
          hchild_small i hi x (by simpa [concat, brouwerCompactU_concat] using hx)
            y (by simpa [concat, brouwerCompactU_concat] using hy)
        simpa [concat, brouwerCompactU_concat] using hsmall

theorem brouwerCompactK_ge_two_of_mem [Nonempty X]
    (hzero : IsZeroDimensional X) (hbounded : ∀ x y : X, dist x y ≤ 1)
    {s : finseq ℕ} (hs : s ∈ boundedBranchingTree (brouwerCompactK hzero)) :
    2 ≤ brouwerCompactK hzero s := by
  rcases brouwerCompactU_node_props_of_mem (X := X) hzero hbounded s hs with
    ⟨hclopen, hnonempty, _hdist⟩
  exact (brouwerStep_spec (X := X) hzero (n := s.length) hclopen hnonempty).1

theorem brouwerCompact_boundedBranchingSchemeCore [Nonempty X]
    (hzero : IsZeroDimensional X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    BoundedBranchingSchemeCore (brouwerCompactK hzero) (brouwerCompactU hzero) where
  root_eq := brouwerCompactU_nil hzero
  nonempty := by
    intro s hs
    exact (brouwerCompactU_node_props_of_mem (X := X) hzero hbounded s hs).2.1
  clopen := by
    intro s hs
    exact (brouwerCompactU_node_props_of_mem (X := X) hzero hbounded s hs).1
  children_cover := by
    intro s hs
    rcases brouwerCompactU_node_props_of_mem (X := X) hzero hbounded s hs with
      ⟨hclopen, hnonempty, _hdist⟩
    rcases brouwerStep_spec (X := X) hzero (n := s.length) hclopen hnonempty with
      ⟨_hk, _hchild_clopen, _hchild_nonempty, _hchild_subset, _hchild_small,
        _hempty, hcover, _hdisjoint⟩
    simpa [brouwerCompactK, brouwerCompactU_concat] using hcover
  children_disjoint := by
    intro s hs i j hij
    rcases brouwerCompactU_node_props_of_mem (X := X) hzero hbounded s hs with
      ⟨hclopen, hnonempty, _hdist⟩
    rcases brouwerStep_spec (X := X) hzero (n := s.length) hclopen hnonempty with
      ⟨_hk, _hchild_clopen, _hchild_nonempty, _hchild_subset, _hchild_small,
        _hempty, _hcover, hdisjoint⟩
    simpa [brouwerCompactK, brouwerCompactU_concat] using hdisjoint i j hij
  dist_bound := by
    intro s hs x hx y hy
    exact (brouwerCompactU_node_props_of_mem (X := X) hzero hbounded s hs).2.2 x hx y hy

theorem exists_brouwer_boundedBranchingSchemeCore [Nonempty X]
    (hzero : IsZeroDimensional X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ∃ k : finseq ℕ → ℕ, ∃ U : finseq ℕ → Set X,
      (∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) ∧
        BoundedBranchingSchemeCore k U := by
  exact ⟨brouwerCompactK hzero, brouwerCompactU hzero,
    fun _s hs => brouwerCompactK_ge_two_of_mem (X := X) hzero hbounded hs,
    brouwerCompact_boundedBranchingSchemeCore (X := X) hzero hbounded⟩

noncomputable def brouwerCompactTreeBodyHomeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    treeBody (boundedBranchingTree (brouwerCompactK hzero)) ≃ₜ X :=
  boundedBranchingSchemeCore_homeomorph hcomplete
    (brouwerCompact_boundedBranchingSchemeCore (X := X) hzero hbounded)

theorem exists_brouwer_boundedBranchingTree_homeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ∃ k : finseq ℕ → ℕ,
      (∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) ∧
        Nonempty (treeBody (boundedBranchingTree k) ≃ₜ X) := by
  exact ⟨brouwerCompactK hzero,
    fun _s hs => brouwerCompactK_ge_two_of_mem (X := X) hzero hbounded hs,
    ⟨brouwerCompactTreeBodyHomeomorph (X := X) hcomplete hzero hbounded⟩⟩

theorem exists_brouwer_perfect_boundedBranchingTree_homeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ∃ k : finseq ℕ → ℕ,
      (∀ ⦃s : finseq ℕ⦄, s ∈ boundedBranchingTree k → 2 ≤ k s) ∧
        IsPruned (boundedBranchingTree k) ∧
          PerfectSpace (treeBody (boundedBranchingTree k)) ∧
            Nonempty (treeBody (boundedBranchingTree k) ≃ₜ X) := by
  refine ⟨brouwerCompactK hzero, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact brouwerCompactK_ge_two_of_mem (X := X) hzero hbounded hs
  · exact boundedBranchingTree_isPruned_of_two_le fun _s hs =>
      brouwerCompactK_ge_two_of_mem (X := X) hzero hbounded hs
  · exact boundedBranchingTree_treeBody_perfect fun _s hs =>
      brouwerCompactK_ge_two_of_mem (X := X) hzero hbounded hs
  · exact ⟨brouwerCompactTreeBodyHomeomorph (X := X) hcomplete hzero hbounded⟩

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: theorem
  title: Brouwer's characterization
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] \emph{The model space.} The Cantor space $\CantorSpace$ is compact by Tychonoff,
    metrizable by the standard sequence metric, zero-dimensional because its cylinders are clopen, and perfect because every
    cylinder has two proper subcylinders.

    \emph{The converse scheme.} Let $X$ be a nonempty compact zero-dimensional perfect metric space, and fix a complete
    compatible metric $d \le 1$. Construct a finitely branching tree $T\IncludedIn\finseq{\omega}$ and a
    \termdefine{Cantor clopen scheme} $\IndexedFamily{U_s}{s\in T}$ of nonempty clopen subsets of $X$ such that:

    \begin{enumerate}
    \item $\emptySeq\in T$ and $U_{\emptySeq}=X$;
    \item the set $\{i\in\omega:s\concat(i)\in T\}$ is finite and has at least two elements for each $s\in T$;
    \item $U_s=\InternalDisjointUnion\{U_{s\concat(i)}: i\in\omega \text{ and } s\concat(i)\in T\}$ for each $s\in T$;
    \item $\MetricDiameter{d}{U_s}\le 2^{-|s|}$.
    \end{enumerate}

    Inductively, suppose $s\in T$ and $U_s$ is already defined. Compactness and zero-dimensionality give a finite clopen
    cover of $U_s$ by sets of diameter $\le 2^{-|s|-1}$. Disjointify the cover and discard empty sets to obtain a finite
    clopen partition with the same diameter bound. If the partition has only one piece, split that piece into two nonempty
    clopen subsets; this is possible because $U_s$ is a nonempty open subspace of a perfect zero-dimensional space. Declare
    the resulting partition to be $\{U_{s\concat(i)}:i<k_s\}$, where $2\le k_s<\omega$, and put those successors into $T$.

    \emph{Applying the common lemma.} The \termuseas{clopen scheme lemma}{clopen-scheme lemma} gives
    $X\cong\TreeBody{T}$. It remains only to identify
    $\TreeBody{T}$ with $\CantorSpace$. At a node $s$, list the immediate successors as
    $s\concat(i_0),\ldots,s\concat(i_{m-1})$, with $m\ge 2$. If the current binary cylinder is $\cyl{q_s}$, split it into
    the $m$ cylinders with stems $q_s\concat c_j$, where
    $$
    c_j=
    \begin{cases}
    \wordRepeat{1}{j}\concat(0),&j+1<m,\\
    \wordRepeat{1}{j},&j+1=m.
    \end{cases}
    $$
    These cylinders are pairwise disjoint and cover $\cyl{q_s}$: a binary tail either has a first $0$ before position
    $m-1$, or it begins with $m-1$ many $1$'s. Assign the cylinder with stem $q_s\concat c_j$ to the successor
    $s\concat(i_j)$. Starting with $q_{\emptySeq}=\emptySeq$ and recursing down the tree produces a binary cylinder scheme
    indexed by $T$, and each successor step appends a nonempty word.

    Now each binary stream determines a unique branch through $T$ by following the unique cylinder that contains it at every
    level. Conversely, a branch through $T$ determines nested binary cylinders whose stem lengths tend to infinity, hence a
    unique binary stream. These assignments are inverse, and the tree cylinder determined by $s$ corresponds to $\cyl{q_s}$.
    The cylinders $\cyl{q_s}$ form a basis for $\CantorSpace$: along the branch determined by any binary stream, their
    stem lengths tend to infinity, so they refine every cylinder neighborhood of that stream. Thus the bijection carries a
    basis of $\TreeBody{T}$ onto a basis of $\CantorSpace$, making both it and its inverse continuous.
    Hence $\CantorSpace\cong\TreeBody{T}$, and therefore $X\cong\CantorSpace$.
    \end{proof}
-/
noncomputable def brouwerCompactCantorHomeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    cantor_space ≃ₜ X :=
  (cantorHomeomorphBoundedBranchingTreeBody
    (fun _s hs => brouwerCompactK_ge_two_of_mem (X := X) hzero hbounded hs)).trans
      (brouwerCompactTreeBodyHomeomorph (X := X) hcomplete hzero hbounded)

theorem exists_brouwer_cantor_homeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    Nonempty (cantor_space ≃ₜ X) :=
  ⟨brouwerCompactCantorHomeomorph (X := X) hcomplete hzero hbounded⟩

end BrouwerCompactConstruction

section AlexandrovUrysohnConstruction

variable {X : Type u} [MetricSpace X] [SecondCountableTopology X]

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    A metric subspace is \termdefine{totally bounded} if, for every $\varepsilon>0$, finitely many open balls of
    radius $\varepsilon$ cover it. We use the standard compactness criterion: a complete metric subspace is compact
    if and only if it is totally bounded.
-/
omit [SecondCountableTopology X] in
theorem totalBoundedness_and_compactness {S : Set X} (hS : IsComplete S) :
    (TotallyBounded S ↔ ∀ ε > 0, ∃ t : Set X, t.Finite ∧ S ⊆ ⋃ y ∈ t, Metric.ball y ε) ∧
      (IsCompact S ↔ TotallyBounded S) :=
  ⟨Metric.totallyBounded_iff,
    ⟨IsCompact.totallyBounded, fun h => h.isCompact_of_isComplete hS⟩⟩

noncomputable def baireStepV (hcomplete : IsMetricComplete X)
    (hzero : IsZeroDimensional X) (hnlc : NoCompactNeighborhoods X)
    (U : Set X) (n : ℕ) : ℕ → Set X :=
  by
    classical
    exact if h : IsClopen U ∧ U.Nonempty then
      Classical.choose (exists_baire_successor_partition (X := X) hcomplete hzero hnlc h.1 h.2 n)
    else fun _ => ∅

theorem baireStep_spec (hcomplete : IsMetricComplete X)
    (hzero : IsZeroDimensional X) (hnlc : NoCompactNeighborhoods X)
    {U : Set X} {n : ℕ} (hU : IsClopen U) (hU_nonempty : U.Nonempty) :
    (∀ i, IsClopen (baireStepV hcomplete hzero hnlc U n i)) ∧
      (∀ i, (baireStepV hcomplete hzero hnlc U n i).Nonempty) ∧
      (∀ i, baireStepV hcomplete hzero hnlc U n i ⊆ U) ∧
      (∀ i, ∀ x ∈ baireStepV hcomplete hzero hnlc U n i,
        ∀ y ∈ baireStepV hcomplete hzero hnlc U n i,
          dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      U = ⋃ i, baireStepV hcomplete hzero hnlc U n i ∧
      Pairwise fun i j => Disjoint
        (baireStepV hcomplete hzero hnlc U n i)
        (baireStepV hcomplete hzero hnlc U n j) := by
  classical
  have h : IsClopen U ∧ U.Nonempty := ⟨hU, hU_nonempty⟩
  simpa [baireStepV, h] using
    Classical.choose_spec
      (exists_baire_successor_partition (X := X) hcomplete hzero hnlc hU hU_nonempty n)

noncomputable def baireSchemeU (hcomplete : IsMetricComplete X)
    (hzero : IsZeroDimensional X) (hnlc : NoCompactNeighborhoods X) :
    finseq ℕ → Set X :=
  fun s =>
    s.reverseRecOn (motive := fun _ => Set X) Set.univ
      (fun t i Ut => baireStepV hcomplete hzero hnlc Ut t.length i)

@[simp]
theorem baireSchemeU_nil (hcomplete : IsMetricComplete X)
    (hzero : IsZeroDimensional X) (hnlc : NoCompactNeighborhoods X) :
    baireSchemeU hcomplete hzero hnlc [] = Set.univ := by
  simp [baireSchemeU]

theorem baireSchemeU_concat (hcomplete : IsMetricComplete X)
    (hzero : IsZeroDimensional X) (hnlc : NoCompactNeighborhoods X)
    (s : finseq ℕ) (i : ℕ) :
    baireSchemeU hcomplete hzero hnlc (concat s [i]) =
      baireStepV hcomplete hzero hnlc (baireSchemeU hcomplete hzero hnlc s) s.length i := by
  simp [baireSchemeU, concat]

theorem baireSchemeU_node_props [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ∀ s : finseq ℕ,
      IsClopen (baireSchemeU hcomplete hzero hnlc s) ∧
        (baireSchemeU hcomplete hzero hnlc s).Nonempty ∧
          ∀ x ∈ baireSchemeU hcomplete hzero hnlc s,
            ∀ y ∈ baireSchemeU hcomplete hzero hnlc s,
              dist x y ≤ (1 / 2 : ℝ) ^ s.length := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [baireSchemeU] using (isClopen_univ : IsClopen (Set.univ : Set X))
      · simp [baireSchemeU,
          (show (Set.univ : Set X).Nonempty from ⟨Classical.arbitrary X, mem_univ _⟩)
        ]
      intro x _ y _
      simpa using hbounded x y
  | append_singleton t i ih =>
      rcases ih with ⟨hclopen, hnonempty, _hdist⟩
      rcases baireStep_spec hcomplete hzero hnlc (n := t.length) hclopen hnonempty with
        ⟨hchild_clopen, hchild_nonempty, _hchild_subset, hchild_small,
          _hcover, _hdisjoint⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [concat, baireSchemeU_concat] using hchild_clopen i
      · simpa [concat, baireSchemeU_concat] using hchild_nonempty i
      · intro x hx y hy
        have hsmall :=
          hchild_small i x (by simpa [concat, baireSchemeU_concat] using hx)
            y (by simpa [concat, baireSchemeU_concat] using hy)
        simpa [concat, baireSchemeU_concat] using hsmall

theorem baireScheme_clopenSchemeMetricCore [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ClopenSchemeMetricCore (Set.univ : Set (finseq ℕ))
      (baireSchemeU hcomplete hzero hnlc) where
  root_mem := mem_univ []
  root_eq := baireSchemeU_nil hcomplete hzero hnlc
  nonempty := by
    intro s _hs
    exact (baireSchemeU_node_props hcomplete hzero hnlc hbounded s).2.1
  clopen := by
    intro s _hs
    exact (baireSchemeU_node_props hcomplete hzero hnlc hbounded s).1
  children_cover := by
    intro s _hs
    rcases baireSchemeU_node_props hcomplete hzero hnlc hbounded s with
      ⟨hclopen, hnonempty, _hdist⟩
    rcases baireStep_spec hcomplete hzero hnlc (n := s.length) hclopen hnonempty with
      ⟨_hchild_clopen, _hchild_nonempty, _hchild_subset, _hchild_small,
        hcover, _hdisjoint⟩
    rw [hcover]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨⟨i, mem_univ _⟩, by
        simpa [baireSchemeU_concat] using hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i.1, by
        simpa [baireSchemeU_concat] using hxi⟩
  children_disjoint := by
    intro s _hs i j hij
    rcases baireSchemeU_node_props hcomplete hzero hnlc hbounded s with
      ⟨hclopen, hnonempty, _hdist⟩
    rcases baireStep_spec hcomplete hzero hnlc (n := s.length) hclopen hnonempty with
      ⟨_hchild_clopen, _hchild_nonempty, _hchild_subset, _hchild_small,
        _hcover, hdisjoint⟩
    have hij_val : i.1 ≠ j.1 := by
      intro hval
      exact hij (Subtype.ext hval)
    simpa [baireSchemeU_concat] using hdisjoint hij_val
  dist_bound := by
    intro s _hs x hx y hy
    exact (baireSchemeU_node_props hcomplete hzero hnlc hbounded s).2.2 x hx y hy

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: statement
  kind: theorem
  title: Theorem (Alexandrov–Urysohn)
-/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] \emph{The model space.} The space $\BaireSpace$ is Polish by §{sec:sequence-spaces} and
    zero-dimensional because cylinders are clopen.
    For nowhere local compactness: every neighborhood of $x$ contains a cylinder $\cyl{s}$, and the sequence $\Sequence{s
    \concat (n)
    \concat \wordRepeat{0}{\omega}}{n\in\omega}$ inside $\cyl{s}$ disagrees pairwise at coordinate $|s|$, so admits no
    convergent subsequence. Any compact set containing this neighborhood would contain the sequence and force
    a convergent subsequence in itself; so no neighborhood of $x$ lies in a compact set.

    \emph{The converse scheme.} Fix a complete compatible metric $d \le 1$ on $X$. Let $T:=\finseq{\omega}$. Construct a
    \termdefine{Baire clopen scheme} $\IndexedFamily{U_s}{s\in T}$ of nonempty clopen subsets of $X$ such that:

    \begin{enumerate}
    \item $\emptySeq\in T$ and $U_{\emptySeq}=X$;
    \item $U_s=\InternalDisjointUnion\{U_{s\concat(n)}: n\in\omega\}$ for each $s\in T$;
    \item $\MetricDiameter{d}{U_s}\le 2^{-|s|}$.
    \end{enumerate}

    Inductively, suppose a nonempty clopen set $U_s$ is given. As an open subspace of $X$, $U_s$ inherits
    zero-dimensionality and nowhere local compactness. The set $U_s$ is not compact: if it were, it would be a compact
    neighborhood of each of its points, contradicting nowhere local compactness of $X$. Since $U_s$ is closed in the
    complete metric space $X$, it is complete; noncompactness therefore means it is not totally bounded. Pick $\epsilon_s >
    0$ such that $U_s$ admits no finite cover by sets of diameter $\le \epsilon_s$, and put
    $\eta_s=\min(2^{-|s|-1},\epsilon_s)$.

    By zero-dimensionality and second countability, choose a countable clopen cover $\IndexedFamily{B_n}{n\in\omega}$ of
    $U_s$ by
    subsets of $U_s$ such that $\MetricDiameter{d}{B_n}\le\eta_s$ for every $n$. Set
    $$
    W_n:=\SetDifference{B_n}{\bigcup_{k<n}B_k}.
    $$
    Each $W_n$ is clopen, $W_n\IncludedIn B_n$, and the $W_n$ are pairwise disjoint. Since the $B_n$ cover $U_s$,
    $$
    U_s=\InternalDisjointUnion_{n\in\omega} W_n
    $$
    after allowing empty pieces, and each $W_n$ has diameter at most $\eta_s$. Infinitely many $W_n$ are nonempty: otherwise
    the nonempty $W_n$ would form a finite cover of $U_s$ by sets of diameter $\le \epsilon_s$, contradicting the choice of
    $\epsilon_s$. Choose a bijective enumeration $e:\omega\to\{n\in\omega:W_n\ne\emptyset\}$ and set
    $U_{s\concat(n)}:=W_{e(n)}$. The resulting successor family is a countable pairwise disjoint clopen cover of $U_s$ by
    nonempty sets, and every successor has diameter at most $2^{-|s|-1}$.

    \emph{Applying the common lemma.} The \termuseas{clopen scheme lemma}{clopen-scheme lemma}, applied to $T$, gives
    $X\cong\TreeBody{\finseq{\omega}}=\BaireSpace$.
    \end{proof}
-/
noncomputable def alexandrovUrysohnBaireHomeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    baire_space ≃ₜ X :=
  (treeBodyUnivHomeomorph (A := ℕ)).symm.trans
    (clopenSchemeMetricCore_branchPointHomeomorph hcomplete
      (univ_isSubtree (A := ℕ))
      (baireScheme_clopenSchemeMetricCore hcomplete hzero hnlc hbounded))

theorem exists_alexandrov_urysohn_baire_homeomorph [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hnlc : NoCompactNeighborhoods X) (hbounded : ∀ x y : X, dist x y ≤ 1) :
    Nonempty (baire_space ≃ₜ X) :=
  ⟨alexandrovUrysohnBaireHomeomorph (X := X) hcomplete hzero hnlc hbounded⟩

end AlexandrovUrysohnConstruction

end SubspaceClassificationProperties

section ModelClassificationProperties

def baireExtendAt (s : finseq ℕ) (n : ℕ) : baire_space :=
  fun i => if hi : i < s.length then s.get ⟨i, hi⟩ else if i = s.length then n else 0

theorem baireExtendAt_mem_cyl (s : finseq ℕ) (n : ℕ) :
    baireExtendAt s n ∈ cyl s := by
  intro i hi
  simp [baireExtendAt, hi]

theorem baireExtendAt_length (s : finseq ℕ) (n : ℕ) :
    baireExtendAt s n s.length = n := by
  simp [baireExtendAt]

theorem cantor_space_perfect :
    PerfectSpace cantor_space :=
  sequence_space_perfect (A := Bool)

theorem baire_space_perfect :
    PerfectSpace baire_space :=
  sequence_space_perfect (A := ℕ)

theorem baire_space_no_compact_nhds (x : baire_space) :
    ¬ ∃ K : Set baire_space, IsCompact K ∧ K ∈ 𝓝 x := by
  rintro ⟨K, hK_compact, hK_nhds⟩
  rcases mem_nhds_iff.mp hK_nhds with ⟨U, hUK, hU_open, hxU⟩
  obtain ⟨s, _hxs, hsU⟩ := exists_cyl_subset_of_mem_open (A := ℕ) hxU hU_open
  have hsK : cyl s ⊆ K := fun y hy => hUK (hsU hy)
  have h_image_univ :
      ((fun y : baire_space => y s.length) '' K : Set ℕ) = Set.univ := by
    refine Set.Subset.antisymm (fun n _ => mem_univ n) ?_
    intro n _hn
    refine ⟨baireExtendAt s n, hsK (baireExtendAt_mem_cyl s n), ?_⟩
    exact baireExtendAt_length s n
  have h_image_compact : IsCompact ((fun y : baire_space => y s.length) '' K) :=
    hK_compact.image (continuous_apply s.length)
  have h_nat_compact : IsCompact (Set.univ : Set ℕ) := by
    simpa [h_image_univ] using h_image_compact
  exact (noncompact_univ ℕ) h_nat_compact

theorem baire_space_noCompactNeighborhoods :
    NoCompactNeighborhoods baire_space :=
  baire_space_no_compact_nhds

noncomputable def cantor_treeBody_univ_homeomorph :
    treeBody (Set.univ : Set (finseq Bool)) ≃ₜ cantor_space :=
  treeBodyUnivHomeomorph (A := Bool)

noncomputable def baire_treeBody_univ_homeomorph :
    treeBody (Set.univ : Set (finseq ℕ)) ≃ₜ baire_space :=
  treeBodyUnivHomeomorph (A := ℕ)

theorem cantor_space_brouwer_hypotheses :
    Nonempty cantor_space ∧
      CompactSpace cantor_space ∧
      PolishSpace cantor_space ∧
      PerfectSpace cantor_space ∧
      IsZeroDimensional cantor_space := by
  exact ⟨inferInstance, inferInstance, cantor_space_polish, cantor_space_perfect,
    cantor_space_zero_dimensional⟩

theorem baire_space_alexandrov_urysohn_hypotheses :
    Nonempty baire_space ∧
      PolishSpace baire_space ∧
      PerfectSpace baire_space ∧
      IsZeroDimensional baire_space ∧
      NoCompactNeighborhoods baire_space := by
  exact ⟨inferInstance, baire_space_polish, baire_space_perfect, baire_space_zero_dimensional,
    baire_space_noCompactNeighborhoods⟩

end ModelClassificationProperties

end PolishSpaceBook
