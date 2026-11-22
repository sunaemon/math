module

public import PolishSpaceBook.SetTheorySequenceExtension
public import PolishSpaceBook.BorelInternalTruth

@[expose] public section

/-! # Set-coded inputs for Borel evaluation on Baire space

The label graph, basis-word graph and point graph are the input parameters.
All finite words and the local relations needed by Boolean evaluation will be
constructed from these parameters inside the model.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open ZFSet SetTheoryModels
universe u

/-- Labels on finite words, represented by their actual function graph. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Let $c$ be a Borel expression, let $b:\omega\to\finseq{\omega}$ specify its basic cylinders, and let
    $x\in\BaireSpace$. Encode these three inputs by
    $$\begin{aligned}
    \ell&:=\{\langle e(s),c(s)\rangle:s\in\finseq{\omega}\},\\
    B&:=\{\langle n,e(b(n))\rangle:n\in\omega\},\\
    g&:=\{\langle n,x(n)\rangle:n\in\omega\}.
    \end{aligned}$$
    Assume these input graphs belong to $M$. No surjectivity of $b$ is needed for evaluation of a fixed code;
    when it enumerates all finite words, its cylinders are the usual base of Baire space.
-/
def labelGraph (c : BorelExpression) : ZFSet.{u} :=
  ZFSet.range (fun s : List ℕ => pair (wordGraph s) (natOrdinal (c s)))

lemma pair_mem_labelGraph (c : BorelExpression) (s : List ℕ) (a : ZFSet.{u}) :
    pair (wordGraph s) a ∈ c.labelGraph ↔ a = natOrdinal (c s) := by
  rw [labelGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨hs, ha⟩ := ZFSet.pair_inj.mp ht
    have hs' := wordGraph_injective hs
    exact hs' ▸ ha.symm
  · rintro rfl
    exact ⟨s, rfl⟩

/-- A sequence of basic cylinders is stored as the graph of its finite words. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Let $c$ be a Borel expression, let $b:\omega\to\finseq{\omega}$ specify its basic cylinders, and let
    $x\in\BaireSpace$. Encode these three inputs by
    $$\begin{aligned}
    \ell&:=\{\langle e(s),c(s)\rangle:s\in\finseq{\omega}\},\\
    B&:=\{\langle n,e(b(n))\rangle:n\in\omega\},\\
    g&:=\{\langle n,x(n)\rangle:n\in\omega\}.
    \end{aligned}$$
    Assume these input graphs belong to $M$. No surjectivity of $b$ is needed for evaluation of a fixed code;
    when it enumerates all finite words, its cylinders are the usual base of Baire space.
-/
def basisWordGraph (b : ℕ → List ℕ) : ZFSet.{u} :=
  ZFSet.range (fun n => pair (natOrdinal n) (wordGraph (b n)))

lemma pair_mem_basisWordGraph (b : ℕ → List ℕ) (n : ℕ) (s : ZFSet.{u}) :
    pair (natOrdinal n) s ∈ basisWordGraph b ↔ s = wordGraph (b n) := by
  rw [basisWordGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨hn, hs⟩ := ZFSet.pair_inj.mp hm
    exact natOrdinal_injective hn ▸ hs.symm
  · rintro rfl
    exact ⟨n, rfl⟩

/-- The graph of a Baire-space point. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Let $c$ be a Borel expression, let $b:\omega\to\finseq{\omega}$ specify its basic cylinders, and let
    $x\in\BaireSpace$. Encode these three inputs by
    $$\begin{aligned}
    \ell&:=\{\langle e(s),c(s)\rangle:s\in\finseq{\omega}\},\\
    B&:=\{\langle n,e(b(n))\rangle:n\in\omega\},\\
    g&:=\{\langle n,x(n)\rangle:n\in\omega\}.
    \end{aligned}$$
    Assume these input graphs belong to $M$. No surjectivity of $b$ is needed for evaluation of a fixed code;
    when it enumerates all finite words, its cylinders are the usual base of Baire space.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $x\in\BaireSpace$, write
    $$g_x:=\{\langle n,x(n)\rangle:n\in\omega\}.$$
-/
def pointGraph (x : ℕ → ℕ) : ZFSet.{u} :=
  ZFSet.range (fun n => pair (natOrdinal n) (natOrdinal (x n)))

lemma pair_mem_pointGraph (x : ℕ → ℕ) (i n : ℕ) :
    pair (natOrdinal i) (natOrdinal n) ∈ pointGraph x ↔ x i = n := by
  rw [pointGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨hi, hn⟩ := ZFSet.pair_inj.mp hj
    exact natOrdinal_injective hi ▸ natOrdinal_injective hn
  · intro h
    exact ⟨i, by rw [h]⟩

/-- Cylinder membership is just inclusion of a finite graph in the point graph. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For the leaves, cylinder membership is the finite graph test
    $$x\in\cyl{b(n)}\quad\Longleftrightarrow\quad e(b(n))\IncludedIn g.$$
-/
lemma wordGraph_subset_pointGraph (s : List ℕ) (x : ℕ → ℕ) :
    wordGraph s ⊆ pointGraph x ↔ x ∈ cyl s := by
  constructor
  · intro h i hi
    exact (pair_mem_pointGraph x i (s.get ⟨i, hi⟩)).mp
      (h (pair_mem_wordGraph.mpr ⟨hi, rfl⟩))
  · intro h p hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    exact (pair_mem_pointGraph x i.val (s.get i)).mpr (h i.val i.isLt)

/-- The nodes carrying a specified label. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    The two label sets are
    $$U:=\{s\in T:\langle s,1\rangle\in\ell\},\qquad
    C:=\{s\in T:\langle s,2\rangle\in\ell\}.$$
-/
def labelSlice (l a : ZFSet.{u}) : ZFSet.{u} :=
  finiteSequences.sep (fun s => pair s a ∈ l)

lemma mem_labelSlice (c : BorelExpression) (s : List ℕ) (n : ℕ) :
    wordGraph s ∈ labelSlice c.labelGraph (natOrdinal n) ↔ c s = n := by
  rw [labelSlice, ZFSet.mem_sep, pair_mem_labelGraph]
  exact ⟨fun h => (natOrdinal_injective h.2).symm,
    fun h => ⟨mem_finiteSequences.mpr ⟨s, rfl⟩, congrArg natOrdinal h.symm⟩⟩

/-- The actual live-child relation, before proving its internal closure. -/
def LiveChild (l t s : ZFSet.{u}) : Prop :=
  ImmediateWordExtension t s ∧
    (∃ a ∈ Ordinal.omega0.toZFSet, pair t a ∈ l ∧ a ≠ natOrdinal 0) ∧
    ∃ a ∈ Ordinal.omega0.toZFSet, pair s a ∈ l ∧ a ≠ natOrdinal 0

lemma liveChild_labelGraph (c : BorelExpression) (t s : List ℕ) :
    LiveChild c.labelGraph (wordGraph t) (wordGraph s) ↔ c.Child t s := by
  have hl (w : List ℕ) :
      (∃ a ∈ Ordinal.omega0.toZFSet, pair (wordGraph w) a ∈ c.labelGraph ∧ a ≠ natOrdinal 0) ↔
        c w ≠ 0 := by
    simp only [pair_mem_labelGraph]
    constructor
    · rintro ⟨a, _, rfl, ha⟩ he
      exact ha (congrArg natOrdinal he)
    · intro h
      exact ⟨natOrdinal (c w), mem_omegaOrdinal.mpr ⟨c w, rfl⟩, rfl,
        fun he => h (natOrdinal_injective he)⟩
  rw [LiveChild, immediateWordExtension_iff, hl t, hl s]
  unfold Child
  constructor
  · rintro ⟨⟨k, hk⟩, ht, hs⟩
    exact ⟨hs, k, hk, ht⟩
  · rintro ⟨hs, k, hk, ht⟩
    exact ⟨⟨k, hk⟩, ht, hs⟩

/-- The true leaves are selected using only graph membership and inclusion. -/
def TrueLeaf (l b x s : ZFSet.{u}) : Prop :=
  ∃ n : ℕ, pair s (natOrdinal (n + 3)) ∈ l ∧
    ∃ w ∈ finiteSequences, pair (natOrdinal n) w ∈ b ∧ w ⊆ x

lemma trueLeaf_labelGraph (c : BorelExpression) (b : ℕ → List ℕ) (x : ℕ → ℕ) (s : List ℕ) :
    TrueLeaf c.labelGraph (basisWordGraph b) (pointGraph x) (wordGraph s) ↔
      3 ≤ c s ∧ x ∈ cyl (b (c s - 3)) := by
  simp only [TrueLeaf, pair_mem_labelGraph, pair_mem_basisWordGraph]
  constructor
  · rintro ⟨n, hn, w, _, rfl, hw⟩
    have he := natOrdinal_injective hn
    have hx := (wordGraph_subset_pointGraph (b n) x).mp hw
    have hc : c s - 3 = n := by omega
    exact ⟨by omega, hc ▸ hx⟩
  · rintro ⟨hc, hx⟩
    refine ⟨c s - 3, congrArg natOrdinal (by omega), wordGraph (b (c s - 3)),
      mem_finiteSequences.mpr ⟨_, rfl⟩, rfl, ?_⟩
    exact (wordGraph_subset_pointGraph _ _).mpr hx

end PolishSpaceBook.BorelExpression
