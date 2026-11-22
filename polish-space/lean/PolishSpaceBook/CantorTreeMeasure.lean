module

public import PolishSpaceBook.RandomGenericReals
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! # Finite-level cuts for measures of binary trees

The measure of a closed tree body is determined by a sequence of rational
numbers obtained by counting finite binary words. No measure on the set of a
model's old points is used in this construction.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- The finite binary words of length `n` that are allowed by the tree. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    We next isolate the numerical part of measure comparison. Let $\mu$ be fair-coin measure on $\CantorSpace$.
    For a downward-closed binary tree $T$, put
    $$\begin{aligned}
    T_n&:=T\cap\funcspace{n}{2},\qquad C_n(T):=\bigcup_{s\in T_n}\cyl{s},\\
    d_n(T)&:=\frac{|T_n|}{2^n}\in\QQ.
    \end{aligned}$$
    We allow the empty tree and dead ends. The definition uses the entire finite level, not just nodes known to
    extend to infinite branches.
-/
def level (T : Set (List Bool)) (n : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun s => List.ofFn s ∈ T)

/-- The clopen approximation obtained from a single finite level. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    We next isolate the numerical part of measure comparison. Let $\mu$ be fair-coin measure on $\CantorSpace$.
    For a downward-closed binary tree $T$, put
    $$\begin{aligned}
    T_n&:=T\cap\funcspace{n}{2},\qquad C_n(T):=\bigcup_{s\in T_n}\cyl{s},\\
    d_n(T)&:=\frac{|T_n|}{2^n}\in\QQ.
    \end{aligned}$$
    We allow the empty tree and dead ends. The definition uses the entire finite level, not just nodes known to
    extend to infinite branches.
-/
def levelSet (T : Set (List Bool)) (n : ℕ) : Set (ℕ → Bool) :=
  ⋃ s ∈ level T n, cyl (List.ofFn s)

lemma mem_levelSet (T : Set (List Bool)) (n : ℕ) (x : ℕ → Bool) :
    x ∈ levelSet T n ↔ seqPrefix x n ∈ T := by
  classical
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    have he := seqPrefix_eq_of_mem_cyl hx
    simp only [List.length_ofFn] at he
    exact he ▸ (Finset.mem_filter.mp hs).2
  · intro hx
    refine mem_iUnion₂.mpr ⟨fun i => x i, ?_, ?_⟩
    · simpa [level, seqPrefix] using hx
    · exact mem_cyl_seqPrefix x n

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Downward closure makes $C_n(T)$ decrease with $n$,
-/
lemma levelSet_antitone {T : Set (List Bool)} (hT : IsSubtree T) :
    Antitone (levelSet T) := by
  intro m n hmn x hx
  exact (mem_levelSet T m x).mpr
    (hT ((mem_levelSet T n x).mp hx) (seqPrefix_prefixOf_of_le x hmn))

lemma isOpen_levelSet (T : Set (List Bool)) (n : ℕ) : IsOpen (levelSet T n) :=
  isOpen_biUnion (fun s _ => isOpen_cyl (List.ofFn s))

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    The finite union $C_n(T)$ is clopen.
-/
lemma isClopen_levelSet (T : Set (List Bool)) (n : ℕ) : IsClopen (levelSet T n) :=
  ⟨isClosed_biUnion_finset (fun s _ => isClosed_cyl (List.ofFn s)), isOpen_levelSet T n⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    and the definition of a branch gives
    $$\TreeBody{T}=\bigcap_n C_n(T).$$
-/
lemma treeBody_eq_iInter (T : Set (List Bool)) : treeBody T = ⋂ n, levelSet T n := by
  ext x
  simp only [mem_iInter, mem_levelSet, mem_treeBody]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Distinct words of length $n$ have disjoint cylinders, each of measure $2^{-n}$.
-/
lemma level_cylinders_disjoint (n : ℕ) :
    Pairwise (fun s t : Fin n → Bool => Disjoint (cyl (List.ofFn s)) (cyl (List.ofFn t))) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro x hs ht
  have hs' := seqPrefix_eq_of_mem_cyl hs
  have ht' := seqPrefix_eq_of_mem_cyl ht
  simp only [List.length_ofFn] at hs' ht'
  exact hst (List.ofFn_inj.mp (hs'.symm.trans ht'))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Finite additivity gives
    $\mu(C_n(T))=d_n(T)$.
-/
lemma measure_levelSet (T : Set (List Bool)) (n : ℕ) :
    fairCoinProduct (levelSet T n) = (level T n).card * (1 / 2 : ℝ≥0∞) ^ n := by
  classical
  rw [levelSet, measure_biUnion_finset
    (fun _ _ _ _ h => level_cylinders_disjoint n h)
    (fun s _ => (isOpen_cyl (List.ofFn s)).measurableSet)]
  simp only [fairCoinProduct_cyl, List.length_ofFn, Finset.sum_const, nsmul_eq_mul]

/-- The dyadic rational attached to a finite level; dead ends may be counted. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    We next isolate the numerical part of measure comparison. Let $\mu$ be fair-coin measure on $\CantorSpace$.
    For a downward-closed binary tree $T$, put
    $$\begin{aligned}
    T_n&:=T\cap\funcspace{n}{2},\qquad C_n(T):=\bigcup_{s\in T_n}\cyl{s},\\
    d_n(T)&:=\frac{|T_n|}{2^n}\in\QQ.
    \end{aligned}$$
    We allow the empty tree and dead ends. The definition uses the entire finite level, not just nodes known to
    extend to infinite branches.
-/
def levelWeight (T : Set (List Bool)) (n : ℕ) : ℚ := (level T n).card * (1 / 2 : ℚ) ^ n

lemma levelWeight_eq_measureReal (T : Set (List Bool)) (n : ℕ) :
    (levelWeight T n : ℝ) = fairCoinProduct.real (levelSet T n) := by
  rw [Measure.real, measure_levelSet]
  simp [levelWeight, ENNReal.toReal_mul, ENNReal.toReal_pow]

lemma levelWeight_nonneg (T : Set (List Bool)) (n : ℕ) : 0 ≤ (levelWeight T n : ℝ) := by
  rw [levelWeight_eq_measureReal]
  exact measureReal_nonneg

/-- Continuity from above turns the finite cylinder count into the closed measure. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Finite-level formula for closed measure
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Continuity from above in the probability space proves the formula. In particular, dead ends are harmless:
    their cylinders disappear from the decreasing intersection.
-/
theorem measure_treeBody {T : Set (List Bool)} (hT : IsSubtree T) :
    fairCoinProduct (treeBody T) = ⨅ n, (level T n).card * (1 / 2 : ℝ≥0∞) ^ n := by
  rw [treeBody_eq_iInter, (levelSet_antitone hT).measure_iInter
    (fun n => (isOpen_levelSet T n).measurableSet.nullMeasurableSet)
    ⟨0, measure_ne_top fairCoinProduct _⟩]
  simp only [measure_levelSet]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Continuity from above in the probability space proves the formula. In particular, dead ends are harmless:
    their cylinders disappear from the decreasing intersection.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Finite-level formula for closed measure
-/
lemma levelWeight_tendsto {T : Set (List Bool)} (hT : IsSubtree T) :
    Tendsto (fun n => (levelWeight T n : ℝ)) atTop
      (𝓝 (fairCoinProduct.real (treeBody T))) := by
  have h := (ENNReal.tendsto_toReal
    (show fairCoinProduct (⋂ n, levelSet T n) ≠ ⊤ by finiteness)).comp
      (tendsto_measure_iInter_atTop
        (fun n => (isOpen_levelSet T n).measurableSet.nullMeasurableSet)
        (levelSet_antitone hT) ⟨0, measure_ne_top fairCoinProduct _⟩)
  change Tendsto (fun n => fairCoinProduct.real (levelSet T n)) atTop
    (𝓝 (fairCoinProduct.real (⋂ n, levelSet T n))) at h
  simpa only [← treeBody_eq_iInter, ← levelWeight_eq_measureReal] using h

lemma measureReal_treeBody_le_levelWeight (T : Set (List Bool)) (n : ℕ) :
    fairCoinProduct.real (treeBody T) ≤ (levelWeight T n : ℝ) := by
  rw [levelWeight_eq_measureReal]
  apply measureReal_mono _ (measure_ne_top fairCoinProduct _)
  rw [treeBody_eq_iInter]
  exact iInter_subset _ n

/-- The same finite-level limit, expressed as an infimum in the real numbers. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Continuity from above in the probability space proves the formula. In particular, dead ends are harmless:
    their cylinders disappear from the decreasing intersection.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Finite-level formula for closed measure
-/
lemma levelWeight_ciInf {T : Set (List Bool)} (hT : IsSubtree T) :
    (⨅ n, (levelWeight T n : ℝ)) = fairCoinProduct.real (treeBody T) := by
  have hbelow : BddBelow (Set.range (fun n => (levelWeight T n : ℝ))) :=
    ⟨fairCoinProduct.real (treeBody T), by
      rintro _ ⟨n, rfl⟩
      exact measureReal_treeBody_le_levelWeight T n⟩
  apply le_antisymm
  · exact ge_of_tendsto' (levelWeight_tendsto hT) (fun n => ciInf_le hbelow n)
  · exact le_ciInf (measureReal_treeBody_le_levelWeight T)

/-- A strict rational upper bound on closed measure has a finite witness. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Rational cuts for closed and open measures
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The decreasing sequence $d_n(T)$ converges to the closed measure and never falls below it. Therefore a strict
    upper bound holds exactly when it already holds at a finite stage.
-/
theorem closed_upper_cut {T : Set (List Bool)} (hT : IsSubtree T) (q : ℚ) :
    fairCoinProduct.real (treeBody T) < q ↔ ∃ n, levelWeight T n < q := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ((levelWeight_tendsto hT).eventually (eventually_lt_nhds h)).exists
    exact ⟨n, by exact_mod_cast hn⟩
  · rintro ⟨n, hn⟩
    exact (measureReal_treeBody_le_levelWeight T n).trans_lt (by exact_mod_cast hn)

/-- A rational lower bound is the conjunction of the finite-level bounds. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Rational cuts for closed and open measures
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Negation gives the second equivalence,
-/
theorem closed_lower_bound {T : Set (List Bool)} (hT : IsSubtree T) (q : ℚ) :
    (q : ℝ) ≤ fairCoinProduct.real (treeBody T) ↔ ∀ n, q ≤ levelWeight T n := by
  constructor
  · intro h n
    exact_mod_cast h.trans (measureReal_treeBody_le_levelWeight T n)
  · intro h
    by_contra hn
    obtain ⟨n, hlt⟩ := (closed_upper_cut hT q).mp (lt_of_not_ge hn)
    exact (not_lt_of_ge (h n)) hlt

/-- The numerical cut has only one real value, independently of how it is interpreted. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Rational cuts for closed and open measures
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Two different real numbers have a rational strictly between them,
    so they cannot have the same strict rational upper bounds.
-/
theorem closed_upper_cut_unique {T : Set (List Bool)} (hT : IsSubtree T) {r : ℝ}
    (hr : ∀ q : ℚ, r < q ↔ ∃ n, levelWeight T n < q) :
    r = fairCoinProduct.real (treeBody T) := by
  apply le_antisymm
  · by_contra h
    obtain ⟨q, hq, hqr⟩ := exists_rat_btwn (lt_of_not_ge h)
    exact (not_lt_of_ge hqr.le) ((hr q).mpr ((closed_upper_cut hT q).mp hq))
  · by_contra h
    obtain ⟨q, hq, hqr⟩ := exists_rat_btwn (lt_of_not_ge h)
    exact (not_lt_of_ge hqr.le) ((closed_upper_cut hT q).mpr ((hr q).mp hq))

/-- Complementation gives the corresponding finite test for an open measure. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Rational cuts for closed and open measures
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    and subtraction from $1$ gives the third.
-/
theorem open_lower_cut {T : Set (List Bool)} (hT : IsSubtree T) (q : ℚ) :
    (q : ℝ) < fairCoinProduct.real (treeBody T)ᶜ ↔ ∃ n, q < 1 - levelWeight T n := by
  have hc := measureReal_add_measureReal_compl (μ := fairCoinProduct)
    (isClosed_treeBody T).measurableSet
  have hq := closed_upper_cut hT (1 - q)
  simp only [probReal_univ, Rat.cast_sub, Rat.cast_one] at hc hq
  constructor
  · intro h
    obtain ⟨n, hn⟩ := hq.mp (by linarith)
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    have h := hq.mpr ⟨n, by linarith⟩
    linarith

end PolishSpaceBook.CantorTreeMeasure
