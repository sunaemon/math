module

public import PolishSpaceBook.FiniteBorelUniversal
public import Mathlib.Topology.Piecewise

@[expose] public section

/-! # Alternating clopen normal forms and complete finite-rank sets -/

namespace PolishSpaceBook.FiniteBorelNormalForm
open Set TopologicalSpace
open scoped Ordinal
universe u

/-- A right-associated tuple of natural numbers, including the empty tuple. -/
def Tuple : ℕ → Type
  | 0 => Unit
  | n + 1 => ℕ × Tuple n

instance (n : ℕ) : Countable (Tuple n) := by
  induction n with
  | zero => exact inferInstanceAs (Countable Unit)
  | succ n ih => exact inferInstanceAs (Countable (ℕ × Tuple n))

instance (n : ℕ) : Inhabited (Tuple n) := by
  induction n with
  | zero => exact inferInstanceAs (Inhabited Unit)
  | succ n ih => exact inferInstanceAs (Inhabited (ℕ × Tuple n))

/-- Start with a universal quantifier and alternate thereafter.
Negating the remaining formula and its matrix flips every remaining quantifier. -/
def alternating : (n : ℕ) → (Tuple n → Prop) → Prop
  | 0, R => R ()
  | n + 1, R => ∀ i, ¬ alternating n (fun t => ¬ R (i, t))

@[simp] theorem alternating_const (n : ℕ) (p : Prop) : alternating n (fun _ => p) ↔ p := by
  classical
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [alternating, ih]

def quantified {X : Type*} {n : ℕ} (C : Tuple n → Set X) : Set X :=
  {x | alternating n (fun t => x ∈ C t)}

/-- A universal stage is the complement of the union of the opposite stages. -/
theorem quantified_succ {X : Type*} {n : ℕ} (C : Tuple (n + 1) → Set X) :
    quantified C = (⋃ i, quantified (fun t : Tuple n => (C (i, t))ᶜ))ᶜ := by
  ext x
  simp [quantified, alternating]

/-- Each leading quantifier adds exactly the corresponding Borel operation. -/
theorem quantified_mem_pi {X : Type*} [MetricSpace X] (n : ℕ)
    (C : Tuple (n + 1) → Set X) (hC : ∀ t, IsClopen (C t)) :
    quantified C ∈ borelPi (↑n + 1) := by
  classical
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, borelPi_one, mem_ofPred_eq]
    have he : quantified C = ⋂ i, C (i, ()) := by
      ext x
      simp [quantified, alternating]
    rw [he]
    exact isClosed_iInter fun i => (hC (i, ())).isClosed
  | succ n ih =>
    rw [quantified_succ]
    change (⋃ i, quantified (fun t : Tuple (n + 1) => (C (i, t))ᶜ))ᶜᶜ ∈
      borelSigma (↑(n + 1) + 1)
    rw [compl_compl, Nat.cast_succ, borelSigma_succ_iff (by exact le_add_left le_rfl)]
    exact ⟨_, fun i => ih _ (fun t => (hC (i, t)).compl), rfl⟩

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    Induct on $k$. For $k=1$, the set $B$ is closed. Enumerate all finite words as $s_i$ and put
    $$
    C_i:=\begin{cases}
    \SetDifference{\BaireSpace}{\cyl{s_i}},&\cyl{s_i}\IncludedIn\SetDifference{\BaireSpace}{B},\\
    \BaireSpace,&\text{otherwise}.
    \end{cases}
    $$
    Each $C_i$ is clopen and $B=\bigcap_i C_i$, since every point outside $B$ lies in a cylinder contained in its open
    complement. This enumeration handles an empty or finite cylinder cover by inserting copies of the whole space.
-/
/-- Enumerate all cylinders and pad those not contained in the open complement
with the whole space. This also handles empty and finite cylinder covers. -/
theorem closed_normal_form {B : Set baire_space} (hB : IsClosed B) :
    ∃ C : ℕ → Set baire_space, (∀ i, IsClopen (C i)) ∧ B = ⋂ i, C i := by
  classical
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (List ℕ)
  let C : ℕ → Set baire_space := fun i => if cyl (σ i) ⊆ Bᶜ then (cyl (σ i))ᶜ else univ
  refine ⟨C, fun i => ?_, ?_⟩
  · dsimp [C]
    split_ifs
    · exact (isClopen_cyl _).compl
    · exact isClopen_univ
  · ext x
    simp only [mem_iInter]
    constructor
    · intro hx i
      dsimp [C]
      split_ifs with hi
      · exact fun hxi => (hi hxi) hx
      · trivial
    · intro hx
      by_contra hn
      obtain ⟨s, hxs, hs⟩ := exists_cyl_subset_of_mem_open hn hB.isOpen_compl
      obtain ⟨i, rfl⟩ := hσ s
      exact (by simpa [C, hs] using hx i : x ∉ cyl (σ i)) hxs

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: lemma
  title: Finite-rank clopen normal form
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    For the successor step, write $B^c=\bigcup_i F_i$ with every $F_i\in\bPi^0_k$ by the successor-level normalization
    used in §{sec:finite-borel-universal}. Choose a clopen normal form for each $F_i$ by induction. Then
    $$x\in B\quad\Longleftrightarrow\quad\forall i\;x\notin F_i.$$
    Negating each chosen normal form reverses all its quantifiers and complements its clopen matrix.
    Prepending the universal quantifier over $i$ therefore gives the required alternating form of length $k+1$.
-/
/-- Inductively normalise every multiplicative finite level using clopen matrices. -/
theorem normal_form (n : ℕ) {B : Set baire_space} (hB : B ∈ borelPi (↑n + 1)) :
    ∃ C : Tuple (n + 1) → Set baire_space,
      (∀ t, IsClopen (C t)) ∧ B = quantified C := by
  classical
  let := metrizableSpaceMetric baire_space
  induction n generalizing B with
  | zero =>
    obtain ⟨C, hC, he⟩ := closed_normal_form (by simpa [borelPi_one] using hB)
    refine ⟨fun t => C t.1, fun t => hC t.1, ?_⟩
    rw [he]
    ext x
    simp [quantified, alternating]
  | succ n ih =>
    change Bᶜ ∈ borelSigma (↑(n + 1) + 1) at hB
    rw [Nat.cast_succ, borelSigma_succ_iff (by exact le_add_left le_rfl)] at hB
    obtain ⟨F, hF, he⟩ := hB
    choose C hC hFC using fun i => ih (hF i)
    refine ⟨fun t => (C t.1 t.2)ᶜ, fun t => (hC t.1 t.2).compl, ?_⟩
    rw [quantified_succ]
    simp only [compl_compl]
    rw [← iUnion_congr hFC, ← he, compl_compl]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    The matrix $y(n_1,\ldots,n_k)=0$ is clopen. Starting from this matrix, the innermost quantifier gives a closed or
    open set, and each subsequent universal or existential quantifier gives a countable intersection or union.
    Thus the displayed alternating formula puts $P_k$ in $\bPi^0_k$.
-/
/-- The book's complete set: the alternating matrix tests whether a coordinate is zero. -/
def completeSet (k : ℕ) : Set (Tuple k → ℕ) :=
  {y | alternating k (fun t => y t = 0)}

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Write $x_k \in \funcspace{\seqPower{\omega}{k}}{\omega}$ for the $k$-th slice of $x \in \BaireSpace$. For $k\ge 1$, let
    $$
    P_k =
    \{y \in \funcspace{\seqPower{\omega}{k}}{\omega} :
    \forall n_1\,\exists n_2\,\forall n_3\cdots Q n_k\,
    y(n_1,\ldots,n_k)=0\},
    $$
    where the quantifiers alternate and $Q$ is $\forall$ when $k$ is odd and $\exists$ when $k$ is even.
-/
theorem completeSet_mem_pi (n : ℕ) : completeSet (n + 1) ∈ borelPi (↑n + 1) := by
  let := metrizableSpaceMetric (Tuple (n + 1) → ℕ)
  exact quantified_mem_pi n (fun t => {y : Tuple (n + 1) → ℕ | y t = 0})
    (fun t => (isClopen_discrete {0}).preimage (continuous_apply t))

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    For any $B\in\bPi^0_k$, choose its clopen matrix from the preceding lemma and define
    $f:\BaireSpace\to\funcspace{\seqPower{\omega}{k}}{\omega}$ by
    $$
    f(x)(n_1,\ldots,n_k)=
    \begin{cases}
    0,&x\in C_{n_1,\ldots,n_k},\\
    1,&x\notin C_{n_1,\ldots,n_k}.
    \end{cases}
    $$
    Each coordinate of $f$ is continuous because its two fibers are clopen. Therefore $f$ is continuous, and
    $x\in B$ iff $f(x)\in P_k$. This proves completeness.
-/
/-- Encode each clopen matrix entry by zero inside it and one outside it. -/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{completeness of alternating-quantifier sets}
-/
theorem completeSet_hard (n : ℕ) {B : Set baire_space} (hB : B ∈ borelPi (↑n + 1)) :
    ∃ f : baire_space → (Tuple (n + 1) → ℕ), Continuous f ∧ f ⁻¹' completeSet (n + 1) = B := by
  classical
  obtain ⟨C, hC, he⟩ := normal_form n hB
  let f : baire_space → (Tuple (n + 1) → ℕ) := fun x t => if x ∈ C t then 0 else 1
  refine ⟨f, continuous_pi (fun t => ?_), ?_⟩
  · exact Continuous.if (by simp [(hC t).frontier_eq]) continuous_const continuous_const
  · rw [he]
    ext x
    simp [f, completeSet, quantified]

theorem one_not_mem_completeSet (k : ℕ) : (fun _ : Tuple k => 1) ∉ completeSet k := by
  simp [completeSet]


/-- Hardness and the previously proved diagonal witness separate the same finite level. -/
theorem completeSet_not_sigma (n : ℕ) :
    completeSet (n + 1) ∉ borelSigma (↑n + 1 : Ordinal.{u}) := by
  obtain ⟨D, hD, hn⟩ := finite_borel_strictness_baire.{u, u} n
  obtain ⟨f, hf, he⟩ := completeSet_hard n hD
  intro h
  exact hn (he ▸ borelSigma_preimage f hf _ h)

/-- Coordinates of the countable disjoint union of all positive finite powers. -/
abbrev Coordinate := Σ n : ℕ, Tuple (n + 1)

instance : Infinite Coordinate :=
  Infinite.of_injective (fun n : ℕ => (⟨n, default⟩ : Coordinate))
    (fun _ _ h => congrArg Sigma.fst h)

/-- A fixed enumeration only reindexes coordinates; no selection algorithm is claimed. -/
noncomputable def coordinateEquiv : Coordinate ≃ ℕ := Classical.choice inferInstance

noncomputable def slice (n : ℕ) (x : baire_space) : Tuple (n + 1) → ℕ :=
  fun t => x (coordinateEquiv ⟨n, t⟩)

theorem continuous_slice (n : ℕ) : Continuous (slice n) :=
  continuous_pi fun t => continuous_apply (coordinateEquiv ⟨n, t⟩)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    A concrete $\bSigma^0_\omega$ set of no finite rank can be written directly in Baire space. The countable disjoint union
    $$I:=\ExternalDisjointUnion_{k\geq 1}\seqPower{\omega}{k}$$
    is countably infinite. A bijection $I\cong\omega$ reindexes coordinates and gives a homeomorphism
    $$
    \BaireSpace
    \cong \funcspace{I}{\omega}
    \cong \prod_{k\ge 1}\funcspace{\seqPower{\omega}{k}}{\omega}.
    $$
-/
/-- The fixed coordinate enumeration gives the homeomorphism displayed in the book. -/
noncomputable def sliceHomeomorph : baire_space ≃ₜ ((n : ℕ) → Tuple (n + 1) → ℕ) where
  toFun x n := slice n x
  invFun y j := y (coordinateEquiv.symm j).1 (coordinateEquiv.symm j).2
  left_inv x := by
    funext j
    simp [slice]
  right_inv y := by
    funext n t
    change (fun c : Coordinate => y c.1 c.2) (coordinateEquiv.symm (coordinateEquiv ⟨n, t⟩)) = y n t
    rw [coordinateEquiv.symm_apply_apply]
  continuous_toFun := continuous_pi continuous_slice
  continuous_invFun := continuous_pi fun j =>
    (continuous_apply (coordinateEquiv.symm j).2).comp (continuous_apply (coordinateEquiv.symm j).1)

/-- The displayed set A, with slice n carrying the positive rank n+1. -/
def unboundedSet : Set baire_space := ⋃ n, slice n ⁻¹' completeSet (n + 1)

/-- Insert one slice and fill all other slices with constant ones. -/
noncomputable def insertSlice (n : ℕ) (y : Tuple (n + 1) → ℕ) : baire_space :=
  fun j => if h : (coordinateEquiv.symm j).1 = n then y (h ▸ (coordinateEquiv.symm j).2) else 1

theorem continuous_insertSlice (n : ℕ) : Continuous (insertSlice n) := by
  apply continuous_pi
  intro j
  dsimp [insertSlice]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

@[simp] theorem slice_insertSlice_self (n : ℕ) (y : Tuple (n + 1) → ℕ) :
    slice n (insertSlice n y) = y := by
  funext t
  change (fun c : Coordinate => if h : c.1 = n then y (h ▸ c.2) else 1)
    (coordinateEquiv.symm (coordinateEquiv ⟨n, t⟩)) = y t
  rw [coordinateEquiv.symm_apply_apply]
  simp

theorem slice_insertSlice_other (n m : ℕ) (h : m ≠ n) (y : Tuple (n + 1) → ℕ) :
    slice m (insertSlice n y) = fun _ => 1 := by
  funext t
  simp [slice, insertSlice, h]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    For each $k\ge1$, define the continuous map
    $\iota_k:\funcspace{\seqPower{\omega}{k}}{\omega}\to\BaireSpace$ by putting its argument in the $k$-th slice
    and the constant-one function in every other slice. The constant-one function lies outside each $P_j$:
    its innermost zero test is always false, and quantifying this false predicate over the nonempty set $\omega$
    leaves it false at every stage. Hence
    $$\iota_k^{-1}(A)=P_k.$$
-/
/-- A slice is isolated because constant one fails every alternating zero test. -/
theorem insertSlice_preimage (n : ℕ) : insertSlice n ⁻¹' unboundedSet = completeSet (n + 1) := by
  ext y
  simp only [mem_preimage, unboundedSet, mem_iUnion]
  constructor
  · rintro ⟨m, hm⟩
    by_cases h : m = n
    · subst m
      simpa using hm
    · rw [slice_insertSlice_other n m h] at hm
      exact (one_not_mem_completeSet (m + 1) hm).elim
  · intro hy
    exact ⟨n, by simpa using hy⟩

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: theorem
  title: A Borel set of no finite rank
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    Each set $\{x:x_k\in P_k\}$ is the continuous preimage of $P_k$ under the slice projection, so it belongs to
    $\bPi^0_k$. Their countable union $A$ therefore belongs to $\bSigma^0_\omega$.
-/
/-- The ranks of the summands approach omega, so their union belongs to Sigma-zero-omega. -/
theorem unboundedSet_mem_sigma_omega : unboundedSet ∈ borelSigma Ordinal.omega0 := by
  rw [borelSigma, ite_eq_right (not_le.mpr Ordinal.one_lt_omega0)]
  refine ⟨fun n => slice n ⁻¹' completeSet (n + 1), fun n => ?_, rfl⟩
  refine ⟨⟨↑n + 1, le_add_left le_rfl, ?_⟩, ?_⟩
  · simpa only [← Nat.cast_succ] using Ordinal.natCast_lt_omega0 (n + 1)
  · exact borelPi_preimage (slice n) (continuous_slice n) _ (completeSet_mem_pi n)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: theorem
  title: A Borel set of no finite rank
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    If $A\in\bSigma^0_m$, take $k=m$. The preceding preimage equality would imply $P_m\in\bSigma^0_m$.
    By completeness, every $\bPi^0_m$ subset of Baire space would then belong to $\bSigma^0_m$, contradicting the
    diagonal witness from §{sec:finite-borel-universal}.
-/
/-- Isolating the slice of rank n+1 rules out the additive class at that rank. -/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The first failure occurs at $\lambda=\omega$. The correct definition permits sets of the form
    $$
    \bigcup_n A_n
    \qquad\text{with}\qquad
    A_n \in \bPi^0_{\beta_n}(\R),\;\beta_n<\omega,
    $$
    with no finite bound on the ranks $\beta_n$. The naive rule would give only $\bigcup_{m<\omega}\bSigma^0_m(\R)$, the
    sets appearing at some finite level. The construction in §{sec:borel-hierarchy-baire} exhibits a set at level $\omega$
    that lies at no finite level.
-/
theorem unboundedSet_not_sigma (n : ℕ) : unboundedSet ∉ borelSigma (↑n + 1) := by
  intro h
  have hi := borelSigma_preimage (insertSlice n) (continuous_insertSlice n) _ h
  rw [insertSlice_preimage] at hi
  exact completeSet_not_sigma n hi

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: theorem
  title: A Borel set of no finite rank
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    Finally, if $A\in\bPi^0_m$, then
    $A\in\bSigma^0_{m+1}$ by the successor inclusion, which has just been ruled out.
-/
/-- The multiplicative class at a finite rank is contained in the next additive class. -/
theorem unboundedSet_not_pi (n : ℕ) : unboundedSet ∉ borelPi (↑n + 1) := by
  intro h
  have hs := borelPi_subset_borelSigma_succ (le_add_left (le_refl (1 : Ordinal))) h
  exact unboundedSet_not_sigma (n + 1) (by simpa only [Nat.cast_succ] using hs)

end PolishSpaceBook.FiniteBorelNormalForm
