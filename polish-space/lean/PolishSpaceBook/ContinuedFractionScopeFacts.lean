module

public import PolishSpaceBook.MediantContinuedFractions
public import PolishSpaceBook.PartIScope
public import PolishSpaceBook.TopologyScopeFacts

@[expose] public section

/-! # The final-one convention for finite continued fractions -/
namespace PolishSpaceBook

/-- `[0; pref, a] = [0; pref, a-1, 1]` with positive partial quotients. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Every positive rational has a finite continued-fraction expression; except for the one-term integer expressions, the two
    standard finite expressions are related by splitting the last partial quotient:
    $$[a_0; a_1,\ldots,a_n]
    \;=\;
    [a_0; a_1,\ldots,a_{n-1},a_n-1,1]
    \qquad (a_n \ge 2).$$
    The standard convention is to use the left-hand expression, whose last partial quotient is at least $2$. In this section
    we instead use the right-hand expression, the one terminating in $1$:
    $$r = [a_0; a_1,\ldots,a_{n-1},1].$$
    For positive integers this means writing $m = [m-1;1]$.
-/
theorem simpleCFTerminatingTailValue_split_last (pref : finseq positiveNat)
    {a : ℕ} (ha : 2 ≤ a) :
    simpleCFTerminatingTailValue pref (a : ℝ) =
      simpleCFTerminatingTailValue (pref ++ [⟨a - 1, by omega⟩]) 1 := by
  rw [simpleCFTerminatingTailValue_append_singleton]
  congr 1
  norm_num
  exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ a by omega)).symm

/-- Reattach the displayed integer part, keeping every earlier quotient. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Every positive rational has a finite continued-fraction expression; except for the one-term integer expressions, the two
    standard finite expressions are related by splitting the last partial quotient:
    $$[a_0; a_1,\ldots,a_n]
    \;=\;
    [a_0; a_1,\ldots,a_{n-1},a_n-1,1]
    \qquad (a_n \ge 2).$$
    The standard convention is to use the left-hand expression, whose last partial quotient is at least $2$. In this section
    we instead use the right-hand expression, the one terminating in $1$:
    $$r = [a_0; a_1,\ldots,a_{n-1},1].$$
    For positive integers this means writing $m = [m-1;1]$.
-/
theorem simpleCFTerminatingExpressionValue_split_last (a₀ : ℕ) (pref : finseq positiveNat)
    {a : ℕ} (ha : 2 ≤ a) :
    (a₀ : ℝ) + simpleCFTerminatingTailValue pref (a : ℝ) =
      simpleCFTerminatingExpressionValue a₀ (pref ++ [⟨a - 1, by omega⟩]) := by
  rw [simpleCFTerminatingExpressionValue, simpleCFTerminatingTailValue_split_last pref ha]

/-- Existence of the chosen terminating expression follows from the proved
subtractive Euclidean construction of rational cylinder labels. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Every positive rational has a finite continued-fraction expression; except for the one-term integer expressions, the two
    standard finite expressions are related by splitting the last partial quotient:
    $$[a_0; a_1,\ldots,a_n]
    \;=\;
    [a_0; a_1,\ldots,a_{n-1},a_n-1,1]
    \qquad (a_n \ge 2).$$
    The standard convention is to use the left-hand expression, whose last partial quotient is at least $2$. In this section
    we instead use the right-hand expression, the one terminating in $1$:
    $$r = [a_0; a_1,\ldots,a_{n-1},1].$$
    For positive integers this means writing $m = [m-1;1]$.
-/
theorem positive_rational_finalOne_expression (q : ℚ) (hq : 0 < q) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      simpleCFTerminatingExpressionValue a₀ pref = (q : ℝ) := by
  obtain ⟨a₀, pref, h⟩ := sternBrocotFiniteCylinderLabel_surjective_positiveRat q hq
  refine ⟨a₀, pref, ?_⟩
  rw [← sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue, h]

/-- The chosen terminating convention is unique. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Every positive rational has a finite continued-fraction expression; except for the one-term integer expressions, the two
    standard finite expressions are related by splitting the last partial quotient:
    $$[a_0; a_1,\ldots,a_n]
    \;=\;
    [a_0; a_1,\ldots,a_{n-1},a_n-1,1]
    \qquad (a_n \ge 2).$$
    The standard convention is to use the left-hand expression, whose last partial quotient is at least $2$. In this section
    we instead use the right-hand expression, the one terminating in $1$:
    $$r = [a_0; a_1,\ldots,a_{n-1},1].$$
    For positive integers this means writing $m = [m-1;1]$.
-/
theorem finalOne_expression_unique {a₀ b₀ : ℕ} {pref qref : finseq positiveNat}
    (h : simpleCFTerminatingExpressionValue a₀ pref =
      simpleCFTerminatingExpressionValue b₀ qref) : a₀ = b₀ ∧ pref = qref :=
  simpleCFTerminatingExpressionValue_injective h

/-- Integers use the same final-one convention with an empty positive prefix. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Every positive rational has a finite continued-fraction expression; except for the one-term integer expressions, the two
    standard finite expressions are related by splitting the last partial quotient:
    $$[a_0; a_1,\ldots,a_n]
    \;=\;
    [a_0; a_1,\ldots,a_{n-1},a_n-1,1]
    \qquad (a_n \ge 2).$$
    The standard convention is to use the left-hand expression, whose last partial quotient is at least $2$. In this section
    we instead use the right-hand expression, the one terminating in $1$:
    $$r = [a_0; a_1,\ldots,a_{n-1},1].$$
    For positive integers this means writing $m = [m-1;1]$.
-/
theorem positive_integer_finalOne_expression {m : ℕ} (hm : 0 < m) :
    simpleCFTerminatingExpressionValue (m - 1) [] = (m : ℝ) :=
  simpleCFTerminatingExpressionValue_empty_positiveInteger hm

/-- The two endpoints after appending `k` are adjacent semiconvergents of the
previous prefix. The earlier convergent coefficients are retained. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    $$
    \theta_{a_0}^{-1}(\cyl{s \concat (k)})
    \;=\;
    \begin{cases}
    \SetDifference{\left(a_0 + F_s(k+1), a_0 + F_s(k)\right)}{\QQ}, & n \text{ even}, \\[0.8em]
    \SetDifference{\left(a_0 + F_s(k), a_0 + F_s(k+1)\right)}{\QQ}, & n \text{ odd}.
    \end{cases}
    $$
-/
theorem simpleCF_child_endpoints {a : ℕ → ℤ} (n k : ℕ)
    (hk : a (n + 1) = (k : ℤ)) :
    simpleCFEndpoint a (n + 1) = (simpleCFSemiconvergent a n k : ℝ) ∧
      simpleCFAdjacentEndpoint a (n + 1) =
        (simpleCFSemiconvergent a n (k + 1) : ℝ) := by
  constructor
  · simp only [simpleCFEndpoint, simpleCFConvergent, simpleCFSemiconvergent,
      simpleCFSemiconvergentNum, simpleCFSemiconvergentDen,
      show n + 1 + 1 = n + 2 by omega, simpleCFNum_succ_succ, simpleCFDen_succ_succ,
      hk, Rat.cast_div, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  · simp only [simpleCFAdjacentEndpoint, simpleCFSemiconvergent,
      simpleCFSemiconvergentNum, simpleCFSemiconvergentDen,
      show n + 1 + 1 = n + 2 by omega, simpleCFNum_succ_succ, simpleCFDen_succ_succ,
      hk, Rat.cast_div, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Nat.cast_add, Nat.cast_one]
    congr 1 <;> push_cast <;> ring

/-- The whole child cylinder, rather than just a one-sided inclusion, is the
irrational interval between the two semiconvergent cut points. Its convergent
coefficients depend only on `pref`, as proved by the prefix-invariance lemmas. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    $$
    \theta_{a_0}^{-1}(\cyl{s \concat (k)})
    \;=\;
    \begin{cases}
    \SetDifference{\left(a_0 + F_s(k+1), a_0 + F_s(k)\right)}{\QQ}, & n \text{ even}, \\[0.8em]
    \SetDifference{\left(a_0 + F_s(k), a_0 + F_s(k+1)\right)}{\QQ}, & n \text{ odd}.
    \end{cases}
    $$
-/
theorem simpleCFFractionalCylinder_child_interval (a₀ : ℤ) (pref : finseq positiveNat)
    (k : positiveNat) :
    let a := positiveNatSeqPartials (extendFinseq (pref ++ [k]))
    Subtype.val '' simpleCFFractionalCylinder a₀ (pref ++ [k]) =
      {y : ℝ | Irrational y ∧ y ∈
        if Even pref.length then
          Set.Ioo ((a₀ : ℝ) + (simpleCFSemiconvergent a pref.length (k.1 + 1) : ℝ))
            ((a₀ : ℝ) + (simpleCFSemiconvergent a pref.length k.1 : ℝ))
        else
          Set.Ioo ((a₀ : ℝ) + (simpleCFSemiconvergent a pref.length k.1 : ℝ))
            ((a₀ : ℝ) + (simpleCFSemiconvergent a pref.length (k.1 + 1) : ℝ))} := by
  let a := positiveNatSeqPartials (extendFinseq (pref ++ [k]))
  have hk : a (pref.length + 1) = (k.1 : ℤ) := by
    have h := extendFinseq_mem_cyl (pref ++ [k]) pref.length (by simp)
    have hs : extendFinseq (pref ++ [k]) pref.length = k := by simpa using h
    simpa only [a, positiveNatSeqPartials] using congrArg (fun x : positiveNat => (x.1 : ℤ)) hs
  obtain ⟨he, hadj⟩ := simpleCF_child_endpoints (a := a) pref.length k.1 hk
  rw [simpleCFFractionalCylinder_eq_tail_image,
    simpleCFTailImageInterval_eq_of_positive a₀ (positiveNatSeqPartials_positive _)]
  dsimp only
  simp only [List.length_append, List.length_singleton]
  change {y : ℝ | Irrational y ∧ y ∈
    if Even (pref.length + 1) then
      Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a (pref.length + 1))
        ((a₀ : ℝ) + simpleCFAdjacentEndpoint a (pref.length + 1))
    else Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a (pref.length + 1))
        ((a₀ : ℝ) + simpleCFEndpoint a (pref.length + 1))} = _
  rw [he, hadj]
  by_cases hn : Even pref.length <;> simp [Nat.even_add_one, hn, a]

/-- All four hypotheses listed in the non-arithmetic irrational-line example. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Irrational line.} The space $\SetDifference{\R}{\QQ}$ is homeomorphic to $\BaireSpace$ by the
    Alexandrov--Urysohn characterization in §{sec:clopen-scheme-characterizations}: it is Polish, zero-dimensional,
    perfect, and nowhere locally compact. The next subsection gives a more explicit and more useful homeomorphism by
    continued-fraction coordinates; in that presentation, basic clopen sets are cylinders that fix finitely many
    partial quotients.
-/
theorem irrationals_characterization_properties :
    PolishSpace {x : ℝ // Irrational x} ∧
      HasSmallInductiveDimensionLE {x : ℝ // Irrational x} 0 ∧
      PerfectSpace {x : ℝ // Irrational x} ∧
      NoCompactNeighborhoods {x : ℝ // Irrational x} :=
  ⟨irrationals_polish,
    (zero_dimensional_iff_small_inductive _).mp irrational_zeroDimensional_via_rational_intervals,
    NoCompactNeighborhoods.perfectSpace irrationals_no_compact_neighborhoods,
    irrationals_no_compact_neighborhoods⟩

/-- Use the existing clopen-scheme/Alexandrov–Urysohn proof, keeping this route
separate from the continued-fraction coordinate construction. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Irrational line.} The space $\SetDifference{\R}{\QQ}$ is homeomorphic to $\BaireSpace$ by the
    Alexandrov--Urysohn characterization in §{sec:clopen-scheme-characterizations}: it is Polish, zero-dimensional,
    perfect, and nowhere locally compact. The next subsection gives a more explicit and more useful homeomorphism by
    continued-fraction coordinates; in that presentation, basic clopen sets are cylinders that fix finitely many
    partial quotients.
-/
theorem irrationals_homeomorphism_from_characterization :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) :=
  irrationals_baire_homeomorphism_via_alexandrov_urysohn

end PolishSpaceBook
