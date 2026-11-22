module

public import PolishSpaceBook.BorelInternalCylinderCodes
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Explicit Borel codes for limits of cylinder-dependent real values

The code uses the book's standard numbering of finite natural words. At a
fixed tolerance, failure of eventual closeness is a countable intersection of
open cylinder unions. A countable union over reciprocal tolerances describes
failure of convergence. Internal membership of the whole code is a separate
obligation; separate membership of its leaves does not suffice.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open Set Filter Topology
open NamedLambda
open scoped Classical

namespace Code

lemma cantor_leaf (n : ℕ) :
    (leaf n).cantor = cantorInclusion ⁻¹' cyl (NatListCode.decode n) := by
  change cantorInclusion ⁻¹' (leaf n).value cylinderBasis = _
  rw [value_leaf]
  rfl

lemma cantor_iInter (c : ℕ → Code) : (iInter c).cantor = ⋂ n, (c n).cantor := by
  simp only [iInter, cantor_compl, cantor_iUnion, compl_iUnion, compl_compl]

/-- Include exactly those numbered cylinders satisfying the specified word test. -/
def selectedCylinders (P : List ℕ → Prop) : Code :=
  iUnion fun j => if P (NatListCode.decode j) then leaf j else empty

lemma mem_selectedCylinders (P : List ℕ → Prop) (x : ℕ → Bool) :
    x ∈ (selectedCylinders P).cantor ↔ ∃ s, P s ∧ cantorInclusion x ∈ cyl s := by
  rw [selectedCylinders, cantor_iUnion]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : P (NatListCode.decode j)
    · rw [ite_eq_left h, cantor_leaf] at hj
      exact ⟨_, h, hj⟩
    · simp only [ite_eq_right h, cantor_empty, mem_empty_iff_false] at hj
  · rintro ⟨s, hs, hx⟩
    refine ⟨NatListCode.encode s, ?_⟩
    rw [NatListCode.decode_encode, ite_eq_left hs, cantor_leaf, NatListCode.decode_encode]
    exact hx

/-- A deviation of size at least 1/(k+1) occurs at some stage beyond N. -/
def deviationTail (f : List ℕ → ℝ) (b : ℝ) (k N : ℕ) : Code :=
  selectedCylinders fun s => N ≤ s.length ∧ 1 / (k + 1 : ℝ) ≤ dist (f s) b

lemma mem_deviationTail (f : List ℕ → ℝ) (b : ℝ) (k N : ℕ) (x : ℕ → Bool) :
    x ∈ (deviationTail f b k N).cantor ↔
      ∃ n ≥ N, 1 / (k + 1 : ℝ) ≤ dist (f (seqPrefix (cantorInclusion x) n)) b := by
  rw [deviationTail, mem_selectedCylinders]
  constructor
  · rintro ⟨s, ⟨hs, hd⟩, hx⟩
    refine ⟨s.length, hs, ?_⟩
    rwa [seqPrefix_eq_of_mem_cyl hx]
  · rintro ⟨n, hn, hd⟩
    exact ⟨_, ⟨by simpa only [seqPrefix_length] using hn, hd⟩, mem_cyl_seqPrefix _ _⟩

/-- Some fixed positive tolerance is violated arbitrarily late. -/
def nonconvergence (f : List ℕ → ℝ) (b : ℝ) : Code :=
  iUnion fun k => iInter fun N => deviationTail f b k N

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $b\in\{0,1\}$ and $k,N\in\omega$, form the open cylinder union
    $$\begin{aligned}
    U^b_{k,N}&:=\bigcup_{\substack{s\in\finseq{2},\ N\le |s|\\ (k+1)^{-1}\le |\mu_s(A)-b|}}\cyl{s},\\
    E_b&:=\bigcup_{k\in\omega}\bigcap_{N\in\omega}U^b_{k,N}.
    \end{aligned}$$
    A point lies in $E_b$ exactly when some fixed positive reciprocal tolerance is violated arbitrarily late.
    Thus a point lies outside $E_b$ exactly when its cylinder densities converge to $b$.
-/
theorem not_mem_nonconvergence (f : List ℕ → ℝ) (b : ℝ) (x : ℕ → Bool) :
    x ∉ (nonconvergence f b).cantor ↔
      Tendsto (fun n => f (seqPrefix (cantorInclusion x) n)) atTop (𝓝 b) := by
  simp only [nonconvergence, cantor_iUnion, cantor_iInter, mem_iUnion, mem_iInter,
    mem_deviationTail]
  push Not
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h k
    exact ⟨N, fun n hn => (hN n hn).trans hk⟩
  · intro h k
    exact h _ (by positivity)

end Code
end PolishSpaceBook.BorelExpression
