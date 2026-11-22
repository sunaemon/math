module

public import PolishSpaceBook.RandomForcing
public import PolishSpaceBook.BorelStructure
public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Order.PFilter

@[expose] public section

/-!
# Forcing and Polish spaces

Formalization targets for `polish-space/src/polish-space-book/forcing-polish-spaces.md`.

The Cohen development includes the dense-set calculations, an explicit
countable descending-chain construction, the unique total real of a filter,
diagonal avoidance, word occurrence, and the dense-open correspondence.
These proofs follow the book and take no generic-existence assumption.
The imported measure-algebra and random-forcing modules prove completeness,
ccc, and the recursive Borel-code calculation. The companion
`RandomGenericReals` module constructs random reals and proves Borel truth
from explicit countable tests. The `InternalRandomRealNames`,
`InternalRandomFilterTransport`, and `InternalBorelTruth` modules implement
internal names, their valuation, and Borel truth for model-generic filters.
General independence claims remain outside this development.
-/

namespace PolishSpaceBook

section CohenForcing

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The poset called \termdefine{Cohen forcing} is
    $$P=\finseq{2}$$
    ordered by extension:
    $$t \le s \quad\Longleftrightarrow\quad s \prefixOf t.$$
    Thus stronger conditions are longer binary strings.
-/
/-- Cohen conditions are finite binary strings. -/
abbrev CohenCondition := List Bool

/-- `t` is a stronger Cohen condition than `s` when `t` extends `s`. -/
def CohenStronger (t s : CohenCondition) : Prop :=
  s.IsPrefix t

/-- A family of Cohen conditions is dense when every condition has a stronger
member of the family. -/
def CohenDense (D : Set CohenCondition) : Prop :=
  ∀ s, ∃ t ∈ D, CohenStronger t s

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For each $n$, put
    $$D_n:=\{s\in\finseq{2}:|s|>n\}.$$
-/
def cohenLengthRequirement (n : ℕ) : Set CohenCondition :=
  {s | n < s.length}

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Length requirements
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Given $s\in\finseq{2}$, append enough zeroes to obtain an extension of length greater than $n$.
    \end{proof}
-/
/-- A condition can always be lengthened enough to decide a prescribed
coordinate. -/
theorem cohenLengthRequirement_dense (n : ℕ) :
    CohenDense (cohenLengthRequirement n) := by
  intro s
  refine ⟨s ++ List.replicate (n + 1) false, ?_, ?_⟩
  · simp [cohenLengthRequirement]
    omega
  · simp [CohenStronger]

/-- A finite condition agrees with an infinite binary sequence on every
coordinate that it has decided. -/
def CohenAgrees (s : CohenCondition) (x : ℕ → Bool) : Prop :=
  ∀ i, i < s.length → s[i]? = some (x i)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For each ground-model real $x\in M\cap\CantorSpace$, put
    $$D_x:=\{s\in\finseq{2}:s\notPrefixOf x\}.$$
-/
def cohenDiagonalRequirement (x : ℕ → Bool) : Set CohenCondition :=
  {s | ¬ CohenAgrees s x}

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Diagonal requirements
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] If $s\notPrefixOf x$, use $s$ itself. If $s\prefixOf x$, extend $s$ by the bit opposite to the
    next bit of $x$.
    \end{proof}
-/
/-- Every condition has an extension that disagrees with a prescribed real. -/
theorem cohenDiagonalRequirement_dense (x : ℕ → Bool) :
    CohenDense (cohenDiagonalRequirement x) := by
  intro s
  by_cases hs : CohenAgrees s x
  · let t := s ++ [!(x s.length)]
    refine ⟨t, ?_, ?_⟩
    · change ¬ CohenAgrees t x
      intro ht
      have hlast := ht s.length (by simp [t])
      simp [t] at hlast
    · simp [CohenStronger, t]
  · exact ⟨s, hs, by simp [CohenStronger]⟩

/-- A finite word occurs as a consecutive block in another finite word. -/
def CohenOccurs (u s : CohenCondition) : Prop :=
  ∃ a b, s = a ++ u ++ b

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Fix a finite word $u\in\finseq{2}$ in $M$. Let
    $$D_u:=\{s\in\finseq{2}:u\text{ occurs as a consecutive block in }s\}.$$
-/
def cohenWordRequirement (u : CohenCondition) : Set CohenCondition :=
  {s | CohenOccurs u s}

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Word-occurrence requirements
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Given any condition $s$, the concatenation $s\concat u$ extends $s$ and belongs to $D_u$.
    \end{proof}
-/
/-- Appending a word meets its occurrence requirement. -/
theorem cohenWordRequirement_dense (u : CohenCondition) :
    CohenDense (cohenWordRequirement u) := by
  intro s
  refine ⟨s ++ u, ?_, ?_⟩
  · exact ⟨s, [], by simp⟩
  · simp [CohenStronger]

end CohenForcing

section CohenGenericReals

/-- Reverse prefix order, kept explicit to avoid changing the order on lists. -/
@[reducible] def cohenOrder : PartialOrder CohenCondition where
  le := CohenStronger
  lt s t := CohenStronger s t ∧ ¬ CohenStronger t s
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl _ := by simp [CohenStronger]
  le_trans _ _ _ hst htu := htu.trans hst
  le_antisymm _ _ hst hts := (hst.eq_of_length_le hts.length_le).symm

/-- Mathlib's order-filter predicate for the Cohen order. No set-theoretic
model is part of this definition. -/
def IsCohenFilter (G : Set CohenCondition) : Prop :=
  @Order.IsPFilter CohenCondition cohenOrder.toPreorder G

/-- The book's three filter conditions are the canonical order-filter property. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    A filter $G\IncludedIn P$ is nonempty, contains every condition weaker than one of its members, and contains a
    common extension of any two of its members.
-/
theorem isCohenFilter_iff (G : Set CohenCondition) :
    IsCohenFilter G ↔ G.Nonempty ∧
      (∀ s ∈ G, ∀ t, CohenStronger s t → t ∈ G) ∧
      ∀ s ∈ G, ∀ t ∈ G, ∃ u ∈ G, CohenStronger u s ∧ CohenStronger u t := by
  let : PartialOrder CohenCondition := cohenOrder
  change Order.IsPFilter G ↔ _
  constructor
  · intro h
    exact ⟨h.toPFilter.nonempty, fun _ hs _ hst => h.toPFilter.mem_of_le hst hs,
      h.toPFilter.directed⟩
  · intro h
    exact Order.IsPFilter.of_def h.1 h.2.2 (fun hst hs => h.2.1 _ hs _ hst)

theorem cohenAgrees_iff_prefixOfSeq (s : CohenCondition) (x : ℕ → Bool) :
    CohenAgrees s x ↔ prefixOfSeq s x := by
  simp only [CohenAgrees, prefixOfSeq, List.get_eq_getElem]
  constructor
  · intro h i hi
    have := h i hi
    simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using this.symm
  · intro h i hi
    simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using (h i hi).symm

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cohen filter union
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For each $n$, choose $s_n\in G$ with $|s_n|>n$ and set $c_G(n)=s_n(n)$. Given $t\in G$ and $n<|t|$, take a common
    extension of $t$ and $s_n$ in $G$. Its $n$th coordinate shows that $t(n)=s_n(n)=c_G(n)$. Thus every $t\in G$ is a
    prefix of $c_G$. The same coordinate argument proves uniqueness, so this sequence is precisely the union $\bigcup G$.
    Conversely, let $t\prefixOf c_G$. Choose $s\in G$ longer than $t$. Both are prefixes of $c_G$, so $t\prefixOf s$.
    Closure toward weaker conditions gives $t\in G$.
-/
/-- Directedness makes all decisions agree; the length tests make them total. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    We first construct its real using just these properties and the length
    requirements; no forcing relation is needed for this construction.
-/
theorem cohen_filter_existsUnique_real {G : Set CohenCondition} (hG : IsCohenFilter G)
    (hlen : ∀ n, ∃ s ∈ G, s ∈ cohenLengthRequirement n) :
    ∃! x : ℕ → Bool, ∀ s ∈ G, CohenAgrees s x := by
  classical
  have hG := (isCohenFilter_iff G).mp hG
  choose s hs hlength using hlen
  have hlt (n) : n < (s n).length := hlength n
  let x : ℕ → Bool := fun n => (s n)[n]'(hlt n)
  have hprefix : ∀ t ∈ G, prefixOfSeq t x := by
    intro t ht i hi
    obtain ⟨u, _, htu, hsu⟩ := hG.2.2 t ht (s i) (hs i)
    change (s i)[i]'(hlt i) = t[i]
    exact (hsu.getElem (hlt i)).trans (htu.getElem hi).symm
  refine ⟨x, fun t ht => (cohenAgrees_iff_prefixOfSeq t x).mpr (hprefix t ht), ?_⟩
  intro y hy
  funext n
  exact (cohenAgrees_iff_prefixOfSeq (s n) y).mp (hy (s n) (hs n)) n (hlt n)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cohen filter union
-/
/-- The filter is exactly the family of finite prefixes of its total real. -/
theorem cohen_filter_eq_prefixes {G : Set CohenCondition} (hG : IsCohenFilter G)
    (hlen : ∀ n, ∃ s ∈ G, s ∈ cohenLengthRequirement n)
    {x : ℕ → Bool} (hx : ∀ s ∈ G, CohenAgrees s x) :
    G = {s | prefixOfSeq s x} := by
  have hG := (isCohenFilter_iff G).mp hG
  ext t
  constructor
  · intro ht
    exact (cohenAgrees_iff_prefixOfSeq t x).mp (hx t ht)
  · intro ht
    obtain ⟨s, hs, hlen'⟩ := hlen t.length
    have hst : prefixOf t s := by
      change t <+: s
      rw [List.prefix_iff_getElem]
      refine ⟨Nat.le_of_lt hlen', ?_⟩
      intro i hi
      exact (ht i hi).symm.trans
        ((cohenAgrees_iff_prefixOfSeq s x).mp (hx s hs) i (lt_trans hi hlen'))
    exact hG.2.1 s hs t hst

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Countable Cohen requirements
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Put $p_0=p$. Given $p_n$, first extend it to a string of length greater than $n$, then use density to choose a
    further extension $p_{n+1}\in E_n$. Put
    $$G=\{s\in P:\exists n\ (s\prefixOf p_n)\}.$$
    This set contains $p$ and is closed toward weaker conditions. If $s\prefixOf p_n$ and $t\prefixOf p_m$, then
    $p_{\max(n,m)}\in G$ extends both, proving directedness. The condition $p_{n+1}$ meets both $E_n$ and $D_n$.
    The preceding lemma supplies the required real. Lengthening before entering $E_n$ is deliberate: a dense set need
    not contain every extension of its members, so lengthening afterwards could leave $E_n$.
-/
/-- Explicit Rasiowa--Sikorski construction, also meeting every length test. -/
theorem cohen_countable_dense_filter (D : ℕ → Set CohenCondition)
    (hD : ∀ n, CohenDense (D n)) (p : CohenCondition) :
    ∃ G : Set CohenCondition, IsCohenFilter G ∧ p ∈ G ∧
      (∀ n, ∃ s ∈ G, s ∈ D n) ∧
      (∀ n, ∃ s ∈ G, s ∈ cohenLengthRequirement n) := by
  classical
  have hstep (n : ℕ) (s : CohenCondition) :
      ∃ t, t ∈ D n ∧ CohenStronger t s ∧ n < t.length := by
    obtain ⟨r, hr, hrs⟩ := cohenLengthRequirement_dense n s
    obtain ⟨t, ht, htr⟩ := hD n r
    exact ⟨t, ht, hrs.trans htr, lt_of_lt_of_le hr htr.length_le⟩
  choose step hstep using hstep
  let chain : ℕ → CohenCondition := Nat.rec p (fun n s => step n s)
  have hsucc (n) : CohenStronger (chain (n + 1)) (chain n) :=
    (hstep n (chain n)).2.1
  have hmono {n m : ℕ} (hnm : n ≤ m) : CohenStronger (chain m) (chain n) := by
    induction m, hnm using Nat.le_induction with
    | base => simp [CohenStronger]
    | succ m _ ih => exact ih.trans (hsucc m)
  let G : Set CohenCondition := {s | ∃ n, CohenStronger (chain n) s}
  have hmem (n) : chain n ∈ G := ⟨n, by simp [CohenStronger]⟩
  refine ⟨G, (isCohenFilter_iff G).mpr ⟨⟨p, hmem 0⟩, ?_, ?_⟩, hmem 0, ?_, ?_⟩
  · rintro s ⟨n, hn⟩ t hst
    exact ⟨n, hst.trans hn⟩
  · rintro s ⟨n, hn⟩ t ⟨m, hm⟩
    exact ⟨chain (max n m), hmem _, hn.trans (hmono (Nat.le_max_left _ _)),
      hm.trans (hmono (Nat.le_max_right _ _))⟩
  · intro n
    exact ⟨chain (n + 1), hmem (n + 1), (hstep n (chain n)).1⟩
  · intro n
    exact ⟨chain (n + 1), hmem (n + 1), (hstep n (chain n)).2.2⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Countable Cohen requirements
-/
/-- Every countable list of dense requirements has a real meeting it, through
any prescribed finite condition. The requirements need not be lower sets. -/
theorem cohen_countable_dense_real (D : ℕ → Set CohenCondition)
    (hD : ∀ n, CohenDense (D n)) (p : CohenCondition) :
    ∃ x : ℕ → Bool, CohenAgrees p x ∧
      ∀ n, ∃ s ∈ D n, CohenAgrees s x := by
  obtain ⟨G, hG, hp, hmeet, hlen⟩ := cohen_countable_dense_filter D hD p
  obtain ⟨x, hx, _⟩ := cohen_filter_existsUnique_real hG hlen
  refine ⟨x, hx p hp, ?_⟩
  intro n
  obtain ⟨s, hs, hsD⟩ := hmeet n
  exact ⟨s, hsD, hx s hs⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: corollary
  title: Newness from diagonal requirements
-/
/-- Meeting a diagonal requirement separates the union real from its target. -/
theorem cohen_real_ne_of_diagonal {G : Set CohenCondition} {x y : ℕ → Bool}
    (hx : ∀ s ∈ G, CohenAgrees s x)
    (hmeet : ∃ s ∈ G, s ∈ cohenDiagonalRequirement y) : x ≠ y := by
  rintro rfl
  obtain ⟨s, hs, hsy⟩ := hmeet
  exact hsy (hx s hs)

/-- A word occurs at a finite offset in an infinite binary sequence. -/
def CohenOccursIn (u : CohenCondition) (x : ℕ → Bool) : Prop :=
  ∃ k, ∀ i, i < u.length → u[i]? = some (x (k + i))

theorem cohen_occursIn_of_agrees {u s : CohenCondition} {x : ℕ → Bool}
    (hu : CohenOccurs u s) (hs : CohenAgrees s x) : CohenOccursIn u x := by
  obtain ⟨a, b, rfl⟩ := hu
  refine ⟨a.length, ?_⟩
  intro i hi
  have h := hs (a.length + i) (by simp; omega)
  simpa [List.getElem?_append, hi, Nat.not_lt.mpr (Nat.le_add_right _ _)] using h

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: corollary
  title: Disjunctiveness from word requirements
-/
/-- Word requirements transfer from finite conditions to their union real. -/
theorem cohen_real_disjunctive {G : Set CohenCondition} {x : ℕ → Bool}
    (hx : ∀ s ∈ G, CohenAgrees s x)
    (hwords : ∀ u, ∃ s ∈ G, s ∈ cohenWordRequirement u) :
    ∀ u, CohenOccursIn u x := by
  intro u
  obtain ⟨s, hs, hu⟩ := hwords u
  exact cohen_occursIn_of_agrees hu (hx s hs)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For Cohen forcing, any real $c$ determines the filter of its finite prefixes
    $$G_c := \{s \in \finseq{2} : s \prefixOf c\}.$$
    It contains the empty string and every shorter prefix of each member. Any two members have a common extension
    in $G_c$, namely the prefix of $c$ whose length is the maximum of their lengths. Thus it is indeed a filter.
-/
/-- A real determines a forcing filter, including all of its finite prefixes. -/
theorem cohen_prefixes_isFilter (x : ℕ → Bool) :
    IsCohenFilter {s | prefixOfSeq s x} := by
  apply (isCohenFilter_iff _).mpr
  refine ⟨⟨[], prefixOfSeq_nil x⟩, ?_, ?_⟩
  · intro s hs t hst
    exact prefixOfSeq_of_prefix hst hs
  · intro s hs t ht
    let n := max s.length t.length
    refine ⟨seqPrefix x n, prefixOfSeq_seqPrefix x n, ?_, ?_⟩
    · have h := seqPrefix_prefixOf_of_le x (Nat.le_max_left s.length t.length)
      rwa [seqPrefix_eq_of_mem_cyl hs] at h
    · have h := seqPrefix_prefixOf_of_le x (Nat.le_max_right s.length t.length)
      rwa [seqPrefix_eq_of_mem_cyl ht] at h

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cohen dense-open correspondence
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The set $U_D$ is open as a union of cylinders. Every nonempty open set contains a cylinder $\cyl{s}$. Density of
    $D$ gives an extension $t\in D$ of $s$, so the nonempty cylinder $\cyl{t}$ lies in both that open set and $U_D$.
    Conversely, density of $U$ gives a point of $\cyl{s}\cap U$. Since this intersection is open, it contains a
    cylinder $\cyl{t}$ about that point. Cylinder inclusion gives $s\prefixOf t$, and $t\in D_U$.
    Finally, $c\in U_D$ means exactly that some $s\in D$ is a prefix of $c$.
-/
/-- A dense condition family gives a dense open union of cylinders. -/
theorem cohen_dense_cylinderCode {D : Set CohenCondition} (hD : CohenDense D) :
    IsOpen (cylinderCode D) ∧ Dense (cylinderCode D) := by
  refine ⟨isOpen_cylinderCode D, dense_iff_inter_open.mpr ?_⟩
  intro U hU ⟨x, hx⟩
  obtain ⟨s, _, hsU⟩ := exists_cyl_subset_of_mem_open hx hU
  obtain ⟨t, htD, hts⟩ := hD s
  obtain ⟨y, hyt⟩ := cyl_nonempty t
  exact ⟨y, hsU (cyl_subset_of_prefix hts hyt),
    mem_cylinderCode.mpr ⟨t, htD, hyt⟩⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cohen dense-open correspondence
-/
/-- Conversely, a dense open set gives a dense family of cylinders inside it. -/
theorem cohen_dense_openCylinderCode {U : Set (ℕ → Bool)}
    (hU : IsOpen U) (hd : Dense U) : CohenDense (openCylinderCode U) := by
  intro s
  obtain ⟨x, hxs, hxU⟩ := hd.inter_open_nonempty (cyl s) (isOpen_cyl s) (cyl_nonempty s)
  have hx : x ∈ cyl s ∩ U := ⟨hxs, hxU⟩
  obtain ⟨t, _, ht⟩ := exists_cyl_subset_of_mem_open hx ((isOpen_cyl s).inter hU)
  exact ⟨t, fun y hy => (ht hy).2,
    prefixOf_of_cyl_subset (fun y hy => (ht hy).1)⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cohen dense-open correspondence
-/
/-- Meeting a condition requirement is exactly membership in its open union. -/
theorem cohen_meets_iff_mem_cylinderCode (D : Set CohenCondition) (x : ℕ → Bool) :
    (∃ s ∈ D, CohenAgrees s x) ↔ x ∈ cylinderCode D := by
  simp only [mem_cylinderCode, mem_cyl, cohenAgrees_iff_prefixOfSeq]

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: corollary
  title: Countable dense-open requirements
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Apply the countable Cohen requirements lemma to $(D_{U_n})$ and $p$. Its real $c\in\cyl{p}$ has, for each $n$,
    a prefix $s\in D_{U_n}$, so $c\in\cyl{s}\IncludedIn U_n$.
-/
/-- The countable construction gives a point in all the dense open sets and in
any prescribed cylinder, without invoking a general Baire-category theorem. -/
theorem cohen_dense_open_intersection (U : ℕ → Set (ℕ → Bool))
    (hU : ∀ n, IsOpen (U n)) (hd : ∀ n, Dense (U n)) (p : CohenCondition) :
    ∃ x ∈ cyl p, ∀ n, x ∈ U n := by
  obtain ⟨x, hx, hmeet⟩ := cohen_countable_dense_real (fun n => openCylinderCode (U n))
    (fun n => cohen_dense_openCylinderCode (hU n) (hd n)) p
  refine ⟨x, (cohenAgrees_iff_prefixOfSeq p x).mp hx, ?_⟩
  intro n
  obtain ⟨s, hs, hxs⟩ := hmeet n
  exact hs ((cohenAgrees_iff_prefixOfSeq s x).mp hxs)

end CohenGenericReals

end PolishSpaceBook
