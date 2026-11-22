module

public import PolishSpaceBook.WadgeHierarchy
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# The first nontrivial Wadge degrees

Clopen membership bits reduce any open set to the binary sequences containing
a one. Conversely, the first one chooses a term of a sequence converging to a
boundary point outside the target open set.
-/

noncomputable section
namespace PolishSpaceBook.WadgeOpenDegrees
open Set Filter Topology
open scoped Classical

abbrev Cantor := ℕ → Fin 2

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Open sets form the first nontrivial non-self-dual Borel pointclass. A useful complete representative in $\CantorSpace$
    is
    $$
    \mathsf O
    :=
    \{x\in\CantorSpace:\exists n\;x(n)=1\}.
    $$
    It is open, being the union of the clopen sets $\{x:x(n)=1\}$, and its complement is the singleton $\{0^\omega\}$.
    To see that it is not closed, let $e_n$ have its only $1$ in coordinate $n$.
    Then $e_n\in\mathsf O$ for every $n$, but $e_n\to0^\omega\notin\mathsf O$.
-/
def openComplete : Set Cantor := {x | ∃ n, x n = 1}
def closedComplete : Set Cantor := openCompleteᶜ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: proposition
  title: $ ^0_1$-complete open set
-/
theorem openComplete_isOpen : IsOpen openComplete := by
  have heq : openComplete = ⋃ n : ℕ, {x : Cantor | x n = 1} := by ext x; simp [openComplete]
  rw [heq]
  exact isOpen_iUnion fun n => (isOpen_discrete ({1} : Set (Fin 2))).preimage (show Continuous (fun x : Cantor => x n) from continuous_apply n)

theorem closedComplete_eq_singleton : closedComplete = {fun _ => 0} := by
  ext x
  simp only [closedComplete, mem_compl_iff, openComplete, mem_ofPred_eq, not_exists, mem_singleton_iff]
  constructor
  · intro h
    funext n
    have hn := h n
    have : (x n).val ≠ 1 := fun h => hn (Fin.ext h)
    apply Fin.ext
    have hlt := (x n).isLt
    change (x n).val = 0
    omega
  · rintro rfl n
    simp

theorem closedComplete_isClosed : IsClosed closedComplete := openComplete_isOpen.isClosed_compl

/-- Move a single one farther and farther out in the binary sequence. -/
def singleOne (n : ℕ) : Cantor := fun k => if k = n then 1 else 0

theorem singleOne_mem (n : ℕ) : singleOne n ∈ openComplete := ⟨n, by simp [singleOne]⟩

theorem singleOne_tendsto : Tendsto singleOne atTop (𝓝 (fun _ => 0)) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  simp [singleOne, show k ≠ n by omega]

theorem openComplete_not_isClosed : ¬ IsClosed openComplete := by
  intro h
  have hz := h.mem_of_tendsto singleOne_tendsto (Eventually.of_forall singleOne_mem)
  simp [openComplete] at hz

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Thus proper closed non-open sets form the dual $\bPi^0_1$ degree. The open and closed complete degrees are not
    equivalent: if $\mathsf O\le_W\mathsf C$, then $\mathsf O$ would be closed, because continuous preimages of closed sets
    are closed.
-/
theorem openComplete_not_reducible_closedComplete :
    ¬ WadgeReducible openComplete closedComplete :=
  fun h => openComplete_not_isClosed (isClosed_of_wadgeReducible h closedComplete_isClosed)

theorem closedComplete_not_reducible_openComplete :
    ¬ WadgeReducible closedComplete openComplete := by
  intro h
  apply openComplete_not_reducible_closedComplete
  simpa [closedComplete] using h.compl

variable {X : Type*} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Let $U\IncludedIn X$ be open. Choose a countable clopen basis $\Sequence{B_n}{n\in\omega}$.
    Put $C_n=B_n$ when $B_n\IncludedIn U$, and put $C_n=\emptyset$ otherwise. The basis property gives
    $$
    U=\bigcup_{n\in\omega}C_n
    $$
    with each $C_n$ clopen. Define $f:X\to\CantorSpace$ by
    $$
    f(x)(n)=
    \begin{cases}
    1, & x\in C_n,\\
    0, & x\notin C_n.
    \end{cases}
    $$
    Each coordinate is continuous because $C_n$ is clopen, hence $f$ is continuous into the product space. By construction,
    $$
    x\in U
    \quad\Longleftrightarrow\quad
    \exists n\;f(x)(n)=1
    \quad\Longleftrightarrow\quad
    f(x)\in\mathsf O.
    $$
    Thus $U=f^{-1}(\mathsf O)$.
-/
/-- Enumerate a countable clopen basis, replacing members outside the open set by the empty set. -/
theorem open_eq_iUnion_clopen [SecondCountableTopology X] (hzero : IsZeroDimensional X)
    {U : Set X} (hU : IsOpen U) :
    ∃ C : ℕ → Set X, (∀ n, IsClopen (C n)) ∧ U = ⋃ n, C n := by
  classical
  obtain ⟨B, hB, hb⟩ := hzero.exists_countable_clopen_basis
  let C : ℕ → Set X := fun n => if B n ⊆ U then B n else ∅
  refine ⟨C, ?_, ?_⟩
  · intro n
    dsimp [C]
    split_ifs
    · exact hB n
    · exact isClopen_empty
  · ext x
    constructor
    · intro hx
      obtain ⟨_, ⟨n, rfl⟩, hxn, hn⟩ := hb.exists_subset_of_mem_open hx hU
      exact mem_iUnion.mpr ⟨n, by simpa [C, hn] using hxn⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      by_cases h : B n ⊆ U
      · exact h (by simpa [C, h] using hn)
      · simp [C, h] at hn

def membershipBits (C : ℕ → Set X) (x : X) : Cantor := fun n => if x ∈ C n then 1 else 0

theorem membershipBits_continuous {C : ℕ → Set X} (hC : ∀ n, IsClopen (C n)) :
    Continuous (membershipBits C) := by
  classical
  apply continuous_pi
  intro n
  change Continuous ((C n).piecewise (fun _ => (1 : Fin 2)) (fun _ => 0))
  apply Continuous.piecewise
  · intro x hx
    rw [(hC n).frontier_eq] at hx
    exact hx.elim
  · exact continuous_const
  · exact continuous_const

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: proposition
  title: $ ^0_1$-complete open set
-/
theorem open_reducible [SecondCountableTopology X] (hzero : IsZeroDimensional X)
    {U : Set X} (hU : IsOpen U) : WadgeReducible U openComplete := by
  obtain ⟨C, hC, hUeq⟩ := open_eq_iUnion_clopen hzero hU
  refine ⟨membershipBits C, membershipBits_continuous hC, ?_⟩
  ext x
  simp [hUeq, openComplete, membershipBits]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Now let $V\IncludedIn Y$ be proper open and not closed. We already have $V\le_W\mathsf O$ by the first part. For the
    converse, choose $y_\infty\in\SetDifference{\Closure{V}}{V}$, and choose a sequence $\Sequence{y_n}{n\in\omega}$ in $V$
    converging to
    $y_\infty$. Define $g:\CantorSpace\to Y$ by
    $$
    g(x)=
    \begin{cases}
    y_n, & n\text{ is the least coordinate with }x(n)=1,\\
    y_\infty, & x=0^\omega.
    \end{cases}
    $$
    The map is continuous away from $0^\omega$: if the first $1$ occurs in coordinate $n$, then its value is fixed
    on the cylinder determined by the first $n+1$ coordinates. To check continuity at $0^\omega$, let $H$ be an open
    neighborhood of $y_\infty$ and choose $N$ such that $y_n\in H$ for all $n\ge N$. If the first $N$ coordinates
    of $x$ are zero, then either $x=0^\omega$ or its first $1$ occurs in a coordinate $n\ge N$.
    In either case $g(x)\in H$. Finally,
    $$
    x\in\mathsf O
    \quad\Longleftrightarrow\quad
    g(x)\in V,
    $$
    so $\mathsf O\le_W V$.
    \end{proof}
-/
/-- The first one selects the term of the convergent sequence. -/
def firstOneMap {Y : Type*} (y : ℕ → Y) (limit : Y) (x : Cantor) : Y :=
  if h : ∃ n, x n = 1 then y (Nat.find h) else limit

theorem firstOneMap_eq_of_prefix {Y : Type*} (y : ℕ → Y) (limit : Y)
    {x z : Cantor} (hx : ∃ n, x n = 1)
    (hz : z ∈ cyl (seqPrefix x (Nat.find hx + 1))) :
    firstOneMap y limit z = firstOneMap y limit x := by
  have hagree : ∀ i < Nat.find hx + 1, z i = x i := by
    intro i hi
    exact (hz i (by simpa using hi)).trans (seqPrefix_get x (by simpa using hi))
  have hex : ∃ n, z n = 1 := ⟨Nat.find hx, (hagree _ (Nat.lt_succ_self _)).trans (Nat.find_spec hx)⟩
  have hfind : Nat.find hex = Nat.find hx := by
    apply le_antisymm
    · exact Nat.find_min' hex ((hagree _ (Nat.lt_succ_self _)).trans (Nat.find_spec hx))
    · by_contra! h
      exact Nat.find_min hx h ((hagree _ (by omega)).symm.trans (Nat.find_spec hex))
  simp [firstOneMap, hx, hex, hfind]

theorem firstOneMap_continuous {Y : Type*} [TopologicalSpace Y]
    {y : ℕ → Y} {limit : Y} (hy : Tendsto y atTop (𝓝 limit)) :
    Continuous (firstOneMap y limit) := by
  apply continuous_def.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  by_cases hex : ∃ n, x n = 1
  · apply Filter.mem_of_superset ((isOpen_cyl (seqPrefix x (Nat.find hex + 1))).mem_nhds
      (mem_cyl_seqPrefix x _))
    intro z hz
    change firstOneMap y limit z ∈ U
    rw [firstOneMap_eq_of_prefix y limit hex hz]
    exact hx
  · have hlim : limit ∈ U := by simpa [firstOneMap, hex] using hx
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.eventually (hU.mem_nhds hlim))
    apply Filter.mem_of_superset ((isOpen_cyl (seqPrefix x N)).mem_nhds (mem_cyl_seqPrefix x N))
    intro z hz
    change firstOneMap y limit z ∈ U
    by_cases hzex : ∃ n, z n = 1
    · have hlarge : N ≤ Nat.find hzex := by
        by_contra! h
        have hzx : z (Nat.find hzex) = x (Nat.find hzex) :=
          (hz _ (by simpa using h)).trans (seqPrefix_get x (by simpa using h))
        exact hex ⟨Nat.find hzex, hzx.symm.trans (Nat.find_spec hzex)⟩
      rw [firstOneMap, dite_eq_left hzex]
      exact hN _ hlarge
    · simpa [firstOneMap, hzex] using hlim

/-- Any convergent sequence inside a set, with its limit outside, supplies the reverse reduction. -/
theorem openComplete_reducible_of_sequence {Y : Type*} [TopologicalSpace Y]
    {V : Set Y} {y : ℕ → Y} {limit : Y} (hyV : ∀ n, y n ∈ V)
    (hlim : limit ∉ V) (hy : Tendsto y atTop (𝓝 limit)) : WadgeReducible openComplete V := by
  refine ⟨firstOneMap y limit, firstOneMap_continuous hy, ?_⟩
  ext x
  by_cases hx : ∃ n, x n = 1
  · simp [openComplete, firstOneMap, hx, hyV]
  · simp [openComplete, firstOneMap, hx, hlim]

theorem openComplete_reducible_of_not_closed {Y : Type*} [TopologicalSpace Y]
    [FirstCountableTopology Y] {V : Set Y} (hV : ¬ IsClosed V) :
    WadgeReducible openComplete V := by
  have hnot : ¬ closure V ⊆ V := by
    intro h
    exact hV (isClosed_of_closure_subset h)
  obtain ⟨limit, hcl, hlim⟩ := Set.not_subset.mp hnot
  obtain ⟨y, hyV, hy⟩ := mem_closure_iff_seq_limit.mp hcl
  exact openComplete_reducible_of_sequence hyV hlim hy

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: proposition
  title: $ ^0_1$-complete open set
-/
theorem open_equivalent [SecondCountableTopology X] [FirstCountableTopology X]
    (hzero : IsZeroDimensional X) {V : Set X} (hV : IsOpen V) (hn : ¬ IsClosed V) :
    WadgeEquivalent V openComplete :=
  ⟨open_reducible hzero hV, openComplete_reducible_of_not_closed hn⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    By complementation, the dual complete closed set is
    $$
    \mathsf C:=\SetDifference{\CantorSpace}{\mathsf O}=\{0^\omega\}.
    $$
-/
theorem closed_reducible [SecondCountableTopology X] (hzero : IsZeroDimensional X)
    {F : Set X} (hF : IsClosed F) : WadgeReducible F closedComplete := by
  simpa [closedComplete] using (open_reducible hzero hF.isOpen_compl).compl

theorem closed_equivalent [SecondCountableTopology X] [FirstCountableTopology X]
    (hzero : IsZeroDimensional X) {F : Set X} (hF : IsClosed F) (hn : ¬ IsOpen F) :
    WadgeEquivalent F closedComplete := by
  have hn' : ¬ IsClosed Fᶜ := by simpa using hn
  obtain ⟨h₁, h₂⟩ := open_equivalent hzero hF.isOpen_compl hn'
  exact ⟨by simpa [closedComplete] using h₁.compl, by simpa [closedComplete] using h₂.compl⟩

end PolishSpaceBook.WadgeOpenDegrees
