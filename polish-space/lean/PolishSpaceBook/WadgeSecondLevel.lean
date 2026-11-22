module

public import PolishSpaceBook.WadgeOpenDegrees
public import PolishSpaceBook.FiniteBorelUniversal
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-!
# Complete sets at the second Borel level

A closed set is an intersection of clopen neighborhoods chosen inside shrinking
metric neighborhoods. Code these neighborhoods as rows of binary coordinates.
An all-zero row means membership in the corresponding closed set.
-/

noncomputable section
namespace PolishSpaceBook
namespace WadgeSecondLevel
open Set Filter Topology
open scoped Classical

abbrev Cantor := WadgeOpenDegrees.Cantor

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    At the next Borel level, the useful normal form is not merely "countable union of closed sets" but "there exists a row
    satisfying a closed condition." Fix a recursive pairing of $\omega\times\omega$ with $\omega$ and define
    $$
    \mathsf S_2
    :=
    \{p\in\CantorSpace:\exists n\;\forall k\; p(\langle n,k\rangle)=0\}.
    $$
    Equivalently, some row of the binary matrix coded by $p$ is constantly zero. This is an $\Fsigma$ set, since
    $$
    \mathsf S_2
    =
    \bigcup_{n\in\omega}
    \bigcap_{k\in\omega}
    \{p:p(\langle n,k\rangle)=0\},
    $$
    a countable union of closed sets.
-/
def sigma2 : Set Cantor := {p | ∃ n, ∀ k, p (Nat.pair n k) = 0}
def pi2 : Set Cantor := sigma2ᶜ

theorem sigma2_isFsigma : IsFsigma sigma2 := by
  let F : ℕ → Set Cantor := fun n => ⋂ k : ℕ, {p | p (Nat.pair n k) = 0}
  refine ⟨range F, countable_range F, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact isClosed_iInter fun k =>
      (isClosed_discrete ({0} : Set (Fin 2))).preimage
        (show Continuous (fun p : Cantor => p (Nat.pair n k)) from continuous_apply _)
  · ext p
    simp [sigma2, F]

theorem sigma2_mem : sigma2 ∈ borelSigma (2 : Ordinal) := by
  simpa [borelSigma_two] using sigma2_isFsigma

theorem pi2_mem : pi2 ∈ borelPi (2 : Ordinal) := by
  simpa [borelPi, pi2] using sigma2_mem

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    The dual complete $\bPi^0_2$ set is
    $$
    \mathsf P_2
    :=
    \SetDifference{\CantorSpace}{\mathsf S_2}
    =
    \{p:\forall n\;\exists k\;p(\langle n,k\rangle)=1\}.
    $$
-/
theorem pi2_eq : pi2 = {p : Cantor | ∀ n, ∃ k, p (Nat.pair n k) = 1} := by
  ext p
  simp only [pi2, sigma2, mem_compl_iff, mem_ofPred_eq, not_exists, not_forall]
  have hbit : ∀ a : Fin 2, a ≠ 0 ↔ a = 1 := by
    intro a
    constructor
    · intro h
      have hv : a.val ≠ 0 := fun hz => h (Fin.ext hz)
      apply Fin.ext
      have ha := a.isLt
      change a.val = 1
      omega
    · rintro rfl
      decide
  simp only [hbit]

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Write $A=\bigcup_n F_n$ with each $F_n$ closed, and fix a compatible metric $d$ on $X$. For each
    $n,k\in\omega$, put
    $$
    O_{n,k}:=\bigcup_{z\in F_n}\MetricBall{d}{z}{2^{-k}}.
    $$
    This is an open set containing $F_n$. The clopen approximation lemma gives a clopen set $V_{n,k}$ with
    $$
    F_n\IncludedIn V_{n,k}\IncludedIn O_{n,k}.
    $$
    This also handles $F_n=\emptyset$: then $O_{n,k}=\emptyset$ and hence $V_{n,k}=\emptyset$.

    These choices satisfy
    $$
    \bigcap_{k\in\omega}V_{n,k}=F_n.
    $$
    The inclusion from right to left holds by construction. If $x\notin F_n$, closedness gives $\varepsilon>0$ such that
    $\MetricBall{d}{x}{\varepsilon}\cap F_n=\emptyset$. Choose $k$ with $2^{-k}<\varepsilon$. A point of $F_n$ at
    distance less than $2^{-k}$ from $x$ would contradict this choice of ball, so $x\notin O_{n,k}$ and hence
    $x\notin V_{n,k}$. This proves the other inclusion.
-/
/-- The neighborhoods use actual nearby points, including when the closed set is empty. -/
theorem closed_eq_iInter_clopen (hzero : IsZeroDimensional X) {F : Set X} (hF : IsClosed F) :
    ∃ V : ℕ → Set X, (∀ k, IsClopen (V k) ∧ F ⊆ V k ∧
      V k ⊆ Metric.thickening ((1 / 2 : ℝ) ^ k) F) ∧ (⋂ k, V k) = F := by
  have hex : ∀ k : ℕ, ∃ V, IsClopen V ∧ F ⊆ V ∧
      V ⊆ Metric.thickening ((1 / 2 : ℝ) ^ k) F := by
    intro k
    exact exists_clopen_between hzero hF Metric.isOpen_thickening
      (Metric.self_subset_thickening (by positivity) F)
  choose V hV using hex
  refine ⟨V, hV, ?_⟩
  apply Subset.antisymm
  · intro x hx
    by_contra hxF
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isOpen_compl x hxF
    have ht : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨k, hk⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
    obtain ⟨z, hzF, hdist⟩ := Metric.mem_thickening_iff.mp ((hV k).2.2 (mem_iInter.mp hx k))
    have hzball : z ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hdist.trans hk
    exact hball hzball hzF
  · exact subset_iInter fun k => (hV k).2.1

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Define $f:X\to\CantorSpace$ by
    $$
    f(x)(\langle n,k\rangle)=
    \begin{cases}
    0, & x\in V_{n,k},\\
    1, & x\notin V_{n,k}.
    \end{cases}
    $$
    The pairing is a bijection, so this prescribes exactly one value at every coordinate. Each coordinate is continuous
    because $V_{n,k}$ is clopen, so $f$ is continuous. For fixed $n$,
    $$
    \forall k\; f(x)(\langle n,k\rangle)=0
    \quad\Longleftrightarrow\quad
    x\in\bigcap_kV_{n,k}
    \quad\Longleftrightarrow\quad
    x\in F_n.
    $$
    Therefore
    $$
    x\in A
    \quad\Longleftrightarrow\quad
    \exists n\;\forall k\;f(x)(\langle n,k\rangle)=0
    \quad\Longleftrightarrow\quad
    f(x)\in\mathsf S_2.
    $$
    Hence $A=f^{-1}(\mathsf S_2)$.
    \end{proof}
-/
/-- Zero records membership in the clopen approximation at the decoded row and column. -/
def rowCode (V : ℕ → ℕ → Set X) (x : X) : Cantor := fun i =>
  if x ∈ V (Nat.unpair i).1 (Nat.unpair i).2 then 0 else 1

omit [MetricSpace X] [SecondCountableTopology X] in
theorem rowCode_pair (V : ℕ → ℕ → Set X) (x : X) (n k : ℕ) :
    rowCode V x (Nat.pair n k) = if x ∈ V n k then 0 else 1 := by
  simp [rowCode]

omit [SecondCountableTopology X] in
theorem rowCode_continuous {V : ℕ → ℕ → Set X} (hV : ∀ n k, IsClopen (V n k)) :
    Continuous (rowCode V) := by
  apply continuous_pi
  intro i
  change Continuous ((V (Nat.unpair i).1 (Nat.unpair i).2).piecewise
    (fun _ => (0 : Fin 2)) (fun _ => 1))
  apply Continuous.piecewise
  · intro x hx
    rw [(hV _ _).frontier_eq] at hx
    exact hx.elim
  · exact continuous_const
  · exact continuous_const

omit [MetricSpace X] [SecondCountableTopology X] in
/-- Decode one all-zero row using the intersection of its clopen approximations. -/
theorem rowCode_zero_iff {F : ℕ → Set X} {V : ℕ → ℕ → Set X}
    (hV : ∀ n, (⋂ k, V n k) = F n) (x : X) (n : ℕ) :
    (∀ k, rowCode V x (Nat.pair n k) = 0) ↔ x ∈ F n := by
  rw [← hV n]
  simp [rowCode_pair]

theorem union_closed_reducible (hzero : IsZeroDimensional X)
    {F : ℕ → Set X} (hF : ∀ n, IsClosed (F n)) : WadgeReducible (⋃ n, F n) sigma2 := by
  choose V hV hVF using fun n => closed_eq_iInter_clopen hzero (hF n)
  refine ⟨rowCode V, rowCode_continuous (fun n k => (hV n k).1), ?_⟩
  ext x
  simp only [mem_iUnion, mem_preimage, sigma2, mem_ofPred_eq, rowCode_zero_iff hVF]

theorem fsigma_reducible (hzero : IsZeroDimensional X)
    {A : Set X} (hA : IsFsigma A) : WadgeReducible A sigma2 := by
  obtain ⟨S, hSc, hS, rfl⟩ := hA
  obtain ⟨F, hF⟩ := (hSc.insert ∅).exists_eq_range (insert_nonempty ∅ S)
  have hclosed : ∀ n, IsClosed (F n) := by
    intro n
    have hn : F n ∈ insert ∅ S := hF ▸ mem_range_self n
    rcases hn with h | h
    · exact h ▸ isClosed_empty
    · exact hS _ h
  have heq : ⋃₀ S = ⋃ n, F n := by rw [← sUnion_range, ← hF]; simp
  rw [heq]
  exact union_closed_reducible hzero hclosed

end WadgeSecondLevel

namespace WadgeSecondLevel
open Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]

/-- The construction applies to every zero-dimensional Polish source space. -/
theorem sigma2_reducible (hzero : IsZeroDimensional X)
    {A : Set X} (hA : A ∈ borelSigma (2 : Ordinal)) : WadgeReducible A sigma2 := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact fsigma_reducible hzero (by simpa [borelSigma_two] using hA)

theorem pi2_reducible (hzero : IsZeroDimensional X)
    {A : Set X} (hA : A ∈ borelPi (2 : Ordinal)) : WadgeReducible A pi2 := by
  simpa [pi2] using (sigma2_reducible hzero hA).compl

theorem cantor_zero_dimensional : IsZeroDimensional Cantor := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.isOpen) ?_
  intro x U hx hU
  obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open hx hU
  exact ⟨cyl s, isClopen_cyl s, hxs, hsU⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Complementing the preceding proposition gives the required reductions to $\mathsf P_2$,
    and $\mathsf P_2$ is a $\Gdelta$ set because $\mathsf S_2$ is $\Fsigma$.
    For strictness, choose a set $T\IncludedIn\CantorSpace$ with
    $$T\in\bSigma^0_2(\CantorSpace),\qquad T\notin\bPi^0_2(\CantorSpace),$$
    as supplied by the diagonal argument in §{sec:borel-hierarchy}. The proposition provides a continuous map
    $\psi:\CantorSpace\to\CantorSpace$ with $T=\psi^{-1}(\mathsf S_2)$. If $\mathsf S_2$ belonged to $\bPi^0_2$,
    closure under continuous preimages would imply $T\in\bPi^0_2(\CantorSpace)$, a contradiction.
    If $\mathsf P_2$ belonged to $\bSigma^0_2$, its complement $\mathsf S_2$ would belong to $\bPi^0_2$.
    \end{proof}
-/
/-- Membership in the dual class would collapse the two pointclasses by continuous preimages. -/
theorem sigma2_not_mem_pi2 : sigma2 ∉ borelPi (2 : Ordinal) := by
  intro h
  obtain ⟨S, hS, hSn⟩ := FiniteBorelUniversal.exists_additive_diagonal (A := Fin 2) 1
  have he : (1 : Ordinal) + 1 = 2 := by exact_mod_cast (by norm_num : (1 : ℕ) + 1 = 2)
  rw [Nat.cast_one, he] at hS hSn
  let : PolishSpace (Fin 2) := (Homeomorph.ofDiscrete finTwoEquiv).isClosedEmbedding.polishSpace
  let : PolishSpace Cantor := countable_product_polish
  obtain ⟨f, hf, heq⟩ := sigma2_reducible cantor_zero_dimensional hS
  apply hSn
  rw [heq]
  exact borelPi_preimage f hf 2 h

theorem pi2_not_mem_sigma2 : pi2 ∉ borelSigma (2 : Ordinal) := by
  intro h
  exact sigma2_not_mem_pi2 h

/-- Both membership and hardness are part of the completeness assertion. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: proposition
  title: $ ^0_2$-complete set
-/
theorem sigma2_complete (hzero : IsZeroDimensional X) :
    sigma2 ∈ borelSigma (2 : Ordinal) ∧
      ∀ A : Set X, A ∈ borelSigma (2 : Ordinal) → WadgeReducible A sigma2 :=
  ⟨sigma2_mem, fun _ hA => sigma2_reducible hzero hA⟩

/-- The dual complete class and the two strict nonmembership assertions. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: corollary
  excerpt: |
    The set $\mathsf P_2$ is $\bPi^0_2$-complete. In particular, in $\CantorSpace$, $\mathsf S_2\notin\bPi^0_2$ and $\mathsf P_2\notin\bSigma^0_2$. \end{corollary*}
-/
theorem pi2_complete_and_strict (hzero : IsZeroDimensional X) :
    (pi2 ∈ borelPi (2 : Ordinal) ∧
      ∀ A : Set X, A ∈ borelPi (2 : Ordinal) → WadgeReducible A pi2) ∧
      sigma2 ∉ borelPi (2 : Ordinal) ∧ pi2 ∉ borelSigma (2 : Ordinal) :=
  ⟨⟨pi2_mem, fun _ hA => pi2_reducible hzero hA⟩, sigma2_not_mem_pi2, pi2_not_mem_sigma2⟩

end WadgeSecondLevel
end PolishSpaceBook
