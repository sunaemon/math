module

public import PolishSpaceBook.MediantContinuedFractions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace PolishSpaceBook

open Set Filter
open scoped Topology

/-- Natural partial quotients with the unused zeroth entry set to zero. -/
def mediantRunPartials (s : ℕ → positiveNat) : ℕ → ℕ
  | 0 => 0
  | n + 1 => s n

theorem mediantRunPartials_cast (s : ℕ → positiveNat) :
    (fun k => (mediantRunPartials s k : ℤ)) = positiveNatSeqPartials s := by
  funext k
  cases k <;> rfl

/-- The two finite-word encodings use the same alternating directions. -/
theorem continuedFractionRunWord_eq_sternBrocot (a₀ : ℕ)
    (s : ℕ → positiveNat) (n : ℕ) :
    continuedFractionRunWord a₀ (mediantRunPartials s) n =
      sternBrocotWordBool (sternBrocotRunLengthWord a₀ (seqPrefix s n)) := by
  induction n with
  | zero => simp [continuedFractionRunWord, seqPrefix, sternBrocotRunLengthWord_empty,
      sternBrocotWordBool, sternBrocotDirectionBool]
  | succ n ih =>
    rw [continuedFractionRunWord, seqPrefix_succ_eq_concat]
    simp only [concat, sternBrocotRunLengthWord_append_singleton,
      sternBrocotWordBool_append, ← ih, seqPrefix_length, mediantRunPartials]
    congr 1
    by_cases hn : Even n
    · have hn' : ¬ Even (n + 1) := by
        rintro ⟨l, hl⟩
        rcases hn with ⟨k, hk⟩
        omega
      simp [sternBrocotWordBool, sternBrocotPartialDirection, hn, hn']
    · have hn' : Even (n + 1) := by
        rcases Nat.not_even_iff_odd.mp hn with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      simp [sternBrocotWordBool, sternBrocotPartialDirection, hn, hn']

/-- The mediant of a run frame is the continued-fraction rational label. -/
theorem continuedFractionRunFrame_split (a₀ : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, 0 < k → 0 < a k) (n : ℕ) :
    (continuedFractionRunFrame a₀ a n).extendedSplit =
      ENNReal.ofReal ((sternBrocotNodeLabel a₀ (fun k => (a k : ℤ)) n : ℚ) : ℝ) := by
  have hb : SimpleCFPositivePartials (fun k => (a k : ℤ)) := by
    intro k
    change (1 : ℤ) ≤ (a (k + 1) : ℤ)
    exact_mod_cast (show 1 ≤ a (k + 1) from ha (k + 1) (by omega))
  have hp := continuedFractionColumn_real_coordinates a₀ a (n + 1)
  have hq := continuedFractionColumn_real_coordinates a₀ a n
  dsimp only at hp hq
  have hcols := continuedFractionRunFrame_columns a₀ a n
  have hs := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
    (p.1.1 + p.2.1, p.1.2 + p.2.2)) hcols
  dsimp only at hs
  have hsum :
      ((continuedFractionRunFrame a₀ a n).a + (continuedFractionRunFrame a₀ a n).c,
       (continuedFractionRunFrame a₀ a n).b + (continuedFractionRunFrame a₀ a n).d) =
      ((continuedFractionColumn a₀ a (n + 1)).1 + (continuedFractionColumn a₀ a n).1,
       (continuedFractionColumn a₀ a (n + 1)).2 + (continuedFractionColumn a₀ a n).2) := by
    split_ifs at hs with hn
    · exact hs
    · simpa [Nat.add_comm] using hs
  have hd : (0 : ℝ) <
      ((continuedFractionColumn a₀ a (n + 1)).2 : ℝ) + (continuedFractionColumn a₀ a n).2 := by
    rw [hp.2, hq.2]
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast simpleCFDen_pos_of_positive hb n)
      (by exact_mod_cast simpleCFDen_nonneg_of_positive hb n)
  have hn := congrArg Prod.fst hsum
  have hden := congrArg Prod.snd hsum
  dsimp only at hn hden
  unfold MediantFrame.extendedSplit
  simp only [hn, hden]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_div_of_pos (by simpa only [Nat.cast_add] using hd)]
  congr 1
  simp only [Nat.cast_add, hp.1, hp.2, hq.1, hq.2, sternBrocotNodeLabel,
    simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen]
  push_cast
  ring

/-- Reading a finite rational's word gives its label as the actual mediant. -/
theorem readMediantWord_finiteCylinder_split (a₀ : ℕ) (pref : finseq positiveNat) :
    (readMediantWord MediantFrame.root
      (sternBrocotWordBool (sternBrocotRunLengthWord a₀ pref))).extendedSplit =
      ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
  have hw := continuedFractionRunWord_eq_sternBrocot a₀ (extendFinseq pref) pref.length
  rw [seqPrefix_eq_of_mem_cyl (extendFinseq_mem_cyl pref)] at hw
  rw [← hw, readMediantWord_runWord, continuedFractionRunFrame_split]
  · rw [mediantRunPartials_cast]
    rfl
  · intro k hk
    cases k with
    | zero => omega
    | succ k => exact (extendFinseq pref : ℕ → positiveNat) k |>.property

theorem mediantIntervalLimit_endpointBelow (w : sternBrocotWord) :
    mediantIntervalLimit (sternBrocotEndpointBelowBranch w) =
      (readMediantWord MediantFrame.root (sternBrocotWordBool w)).extendedSplit := by
  have hm : sternBrocotEndpointBelowBranch w ∈ cyl (sternBrocotWordBool w) := by
    intro i hi
    exact sternBrocotEndpointBelowBranch_prefix w (by simpa using hi)
  have he := mediantBranchFrame_eq_readMediantWord hm
  simp only [sternBrocotWordBool_length] at he
  rw [← he]
  exact (mediantIntervalLimit_eq_split_iff _ _).mpr
    (Or.inl ⟨sternBrocotEndpointBelowBranch_splitCoordinate w,
      fun _ hn => sternBrocotEndpointBelowBranch_tail w hn⟩)

theorem mediantIntervalLimit_endpointAbove (w : sternBrocotWord) :
    mediantIntervalLimit (sternBrocotEndpointAboveBranch w) =
      (readMediantWord MediantFrame.root (sternBrocotWordBool w)).extendedSplit := by
  have hm : sternBrocotEndpointAboveBranch w ∈ cyl (sternBrocotWordBool w) := by
    intro i hi
    exact sternBrocotEndpointAboveBranch_prefix w (by simpa using hi)
  have he := mediantBranchFrame_eq_readMediantWord hm
  simp only [sternBrocotWordBool_length] at he
  rw [← he]
  exact (mediantIntervalLimit_eq_split_iff _ _).mpr
    (Or.inr ⟨sternBrocotEndpointAboveBranch_splitCoordinate w,
      fun _ hn => sternBrocotEndpointAboveBranch_tail w hn⟩)

/-- The start of the `n`-th alternating run. -/
noncomputable def cantorRunStart (b : cantorNonEventuallyConstantBranches) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (cantorBranchRunLength b i).1

theorem cantorRunStart_succ (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    cantorRunStart b (n + 1) = cantorRunStart b n + (cantorBranchRunLength b n).1 :=
  Finset.sum_range_succ _ _

theorem cantorRunStart_eq_change (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    cantorRunStart b (n + 1) =
      infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n + 1 :=
  (cantorBranchChangePointNth_add_one_eq_sum_runLengths b n).symm

/-- No change point occurs in the interior of an enumerated run. -/
theorem cantorRun_no_change (b : cantorNonEventuallyConstantBranches) (n i : ℕ)
    (hlo : cantorRunStart b n ≤ i) (hhi : i + 1 < cantorRunStart b (n + 1)) :
    b.1 i = b.1 (i + 1) := by
  by_contra hne
  have hm : i ∈ ((branchChangePointProductMap b).2 : Set ℕ) := hne
  have hlt : i < infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n := by
    rw [cantorRunStart_eq_change] at hhi
    omega
  cases n with
  | zero =>
    have hle : infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 0 ≤ i := by
      unfold infiniteSubsetsOmegaNth
      rw [Nat.nth_zero]
      exact Nat.sInf_le hm
    exact (not_le_of_gt hlt) hle
  | succ n =>
    have hle : i ≤ infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n :=
      Nat.le_nth_of_lt_nth_succ hlt hm
    rw [cantorRunStart_eq_change] at hlo
    omega

/-- All coordinates of a run have its initial bit. -/
theorem cantorRun_bit (b : cantorNonEventuallyConstantBranches) (n k : ℕ)
    (hk : k < (cantorBranchRunLength b n).1) :
    b.1 (cantorRunStart b n + k) = b.1 (cantorRunStart b n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih (by omega)]
    simpa only [Nat.add_assoc] using
      (cantorRun_no_change b n (cantorRunStart b n + k) (Nat.le_add_right _ _)
        (by rw [cantorRunStart_succ]; omega)).symm

/-- The bit flips precisely when a run ends. -/
theorem cantorRun_flip (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    b.1 (cantorRunStart b (n + 1)) = !b.1 (cantorRunStart b n) := by
  have hp := (cantorBranchRunLength b n).property
  have hlast := cantorRun_bit b n ((cantorBranchRunLength b n).1 - 1) (by omega)
  have he := cantorRunStart_eq_change b n
  have hs := cantorRunStart_succ b n
  have hm := infiniteSubsetsOmegaNth_mem (branchChangePointProductMap b).2 n
  change b.1 (infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n) ≠
    b.1 (infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n + 1) at hm
  have hidx : cantorRunStart b n + ((cantorBranchRunLength b n).1 - 1) =
      infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n := by omega
  rw [hidx] at hlast
  rw [hlast, ← he] at hm
  cases h₀ : b.1 (cantorRunStart b n) <;>
    cases h₁ : b.1 (cantorRunStart b (n + 1)) <;> simp_all

/-- Appending successive full runs gives the finite prefixes of the actual branch.
The offset allows an empty initial right run. -/
theorem continuedFractionRunWord_mem_of_runs (b : cantorNonEventuallyConstantBranches)
    (a₀ offset : ℕ) (s : ℕ → positiveNat)
    (hs : ∀ n, s n = cantorBranchRunLength b (n + offset))
    (hlen : a₀ = cantorRunStart b offset)
    (hinit : b.1 ∈ cyl (List.replicate a₀ true))
    (hbit : b.1 (cantorRunStart b offset) = false) (n : ℕ) :
    b.1 ∈ cyl (continuedFractionRunWord a₀ (mediantRunPartials s) n) ∧
      (continuedFractionRunWord a₀ (mediantRunPartials s) n).length =
        cantorRunStart b (n + offset) ∧
      b.1 (cantorRunStart b (n + offset)) = !decide (Even n) := by
  induction n with
  | zero => simpa [continuedFractionRunWord] using And.intro hinit (And.intro hlen hbit)
  | succ n ih =>
    have hb : (!decide (Even (n + 1))) = !(!decide (Even n)) := by
      simp only [Nat.even_add_one, decide_not, Bool.not_not]
    refine ⟨?_, ?_, ?_⟩
    · rw [continuedFractionRunWord]
      apply mem_cyl_concat_iff.mpr
      refine ⟨ih.1, ?_⟩
      intro k hk
      simp only [List.length_replicate, mediantRunPartials, hs] at hk
      simpa only [ih.2.1, List.get_eq_getElem, List.getElem_replicate] using
        (cantorRun_bit b (n + offset) k hk).trans ih.2.2
    · simp only [continuedFractionRunWord, List.length_append, List.length_replicate,
        mediantRunPartials, ih.2.1, hs]
      simpa only [Nat.add_right_comm n 1 offset] using
        (cantorRunStart_succ b (n + offset)).symm
    · rw [Nat.add_right_comm n 1 offset, cantorRun_flip, ih.2.2]
      exact hb.symm

/-- The run coordinates used by the existing homeomorphism satisfy every finite
prefix condition of the geometric continued-fraction limit theorem. -/
theorem natRunLengthCoordinates_mem_runWord (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    let c := cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b
    b.1 ∈ cyl (continuedFractionRunWord c.1 (mediantRunPartials c.2) n) := by
  cases hi : b.1 0
  · rw [cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse hi]
    exact (continuedFractionRunWord_mem_of_runs b 0 0 (cantorBranchRunLength b)
      (fun _ => rfl) rfl (by intro i hi; simp at hi) hi n).1
  · rw [cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue hi]
    apply (continuedFractionRunWord_mem_of_runs b (cantorBranchRunLength b 0).1 1
      (shiftPositiveNat (cantorBranchRunLength b)) (fun _ => rfl) ?_ ?_ ?_ n).1
    · simp [cantorRunStart]
    · intro k hk
      have h := cantorRun_bit b 0 k (by simpa using hk)
      simpa [cantorRunStart, hi] using h
    · simpa [cantorRunStart, hi] using cantorRun_flip b 0

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For a branch in $S$, completing each run by the first opposite letter fixes a continued-fraction prefix.
    The \termuse{completed-run cylinder lemma} identifies the corresponding $J_w$ with the closure in $\R$ of that
    cylinder. The unique intersection point is therefore the irrational with those partial
    quotients. Hence $\MediantLimitMap$ is a bijection from $S$ onto the positive irrationals, given by
    $$\wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\wordRepeat{L}{a_3}\cdots
    \longleftrightarrow
    (a_0,a_1,a_2,\ldots) \in \NN \times \funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}},$$
    with
    $\MediantLimitMap(\wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\wordRepeat{L}{a_3}\cdots)
    =[a_0;a_1,a_2,\ldots]$.
-/
/-- On non-eventually-constant branches, the interval-defined map is the value
of the continued-fraction homeomorphism with the same run coordinates. -/
theorem mediantIntervalLimit_positiveIrrational (b : cantorNonEventuallyConstantBranches) :
    mediantIntervalLimit b.1 =
      ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 := by
  let c := cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b
  have ht := (simpleCFCoordinateBeta_spec (c.1 : ℤ) c.2).2.2.2
  have ht' : Tendsto (fun n => (simpleCFConvergent (positiveNatSeqPartials c.2) n : ℝ))
      atTop (𝓝 (simpleCFCoordinateBeta (c.1 : ℤ) c.2)) := by
    simpa only [add_sub_cancel_left] using ht.sub_const ((c.1 : ℤ) : ℝ)
  have h := mediantIntervalLimit_of_continuedFractionRuns b.1 c.1 (mediantRunPartials c.2)
    (by intro k hk; cases k with
        | zero => omega
        | succ k => exact (c.2 k).property)
    (natRunLengthCoordinates_mem_runWord b)
    (by simpa only [mediantRunPartials_cast] using ht')
  change mediantIntervalLimit b.1 =
    ENNReal.ofReal (((c.1 : ℤ) : ℝ) + simpleCFCoordinateBeta (c.1 : ℤ) c.2)
  simpa only [Int.cast_natCast] using h

/-- The geometric and branch-classification definitions agree on every branch. -/
theorem mediantIntervalLimit_eq_sternBrocotMediantLimitValue (b : cantor_space) :
    mediantIntervalLimit b = sternBrocotMediantLimitValue b := by
  have h := sternBrocotMediantLimitValue_spec b
  generalize hy : sternBrocotMediantLimitValue b = y at h ⊢
  cases h with
  | allLeft => exact mediantIntervalLimit_allLeft
  | allRight => exact mediantIntervalLimit_allRight
  | finiteEndpointBelow a₀ pref =>
    exact (mediantIntervalLimit_endpointBelow _).trans
      (readMediantWord_finiteCylinder_split a₀ pref)
  | finiteEndpointAbove a₀ pref =>
    exact (mediantIntervalLimit_endpointAbove _).trans
      (readMediantWord_finiteCylinder_split a₀ pref)
  | positiveIrrational b => exact mediantIntervalLimit_positiveIrrational b

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    On the nonconstant eventually constant branches in $\SetDifference{\CantorSpace}{S}$,
    $\MediantLimitMap$ is $2$-to-$1$ onto
    $\RestrictedSet{\QQ}{>0}$. The rational at finite node $b$ has the two endpoint branches
    $b\concat(L)\concat\wordRepeat{R}{\omega}$ and $b\concat(R)\concat\wordRepeat{L}{\omega}$, analogous to the dyadic
    ambiguity $0.0\overline{1}=0.1\overline{0}$.
    
    To see this, let $r$ be the mediant at node $b$. After choosing L, retaining $r$ as an endpoint forces every later
    choice to be R; after choosing R, every later choice must be L. Choosing the other child at any later step excludes
    $r$ from the closed interval. At depth $|b|$, $r$ lies in the interior of $J_b$, so a branch with limit $r$ must
    first pass through $b$. These are therefore its only two preimages. Conversely, every nonconstant eventually-constant
    branch has a last change of letter and hence has one of these two forms.
-/
/-- The interval-defined map has exactly two preimages at each positive rational;
both are eventually-constant endpoint branches. -/
theorem mediantIntervalLimit_positiveRat_exact_endpointPair (q : ℚ) (hq : 0 < q) :
    ∃ bBelow bAbove : cantor_space,
      bBelow ∉ cantorNonEventuallyConstantSet ∧
      bAbove ∉ cantorNonEventuallyConstantSet ∧ bBelow ≠ bAbove ∧
      mediantIntervalLimit bBelow = ENNReal.ofReal (q : ℝ) ∧
      mediantIntervalLimit bAbove = ENNReal.ofReal (q : ℝ) ∧
      ∀ b : cantor_space,
        mediantIntervalLimit b = ENNReal.ofReal (q : ℝ) → b = bBelow ∨ b = bAbove := by
  rcases sternBrocotMediantLimitValue_positiveRat_exact_endpointPair q hq with
    ⟨bBelow, bAbove, hBelow, hAbove, hne, hvBelow, hvAbove, hfiber⟩
  refine ⟨bBelow, bAbove, hBelow, hAbove, hne, ?_, ?_, ?_⟩
  · simpa only [mediantIntervalLimit_eq_sternBrocotMediantLimitValue] using hvBelow
  · simpa only [mediantIntervalLimit_eq_sternBrocotMediantLimitValue] using hvAbove
  · intro b hb
    by_cases hS : b ∈ cantorNonEventuallyConstantSet
    · let c : cantorNonEventuallyConstantBranches := ⟨b, hS⟩
      have he := (mediantIntervalLimit_positiveIrrational c).symm.trans hb
      have hx := (sternBrocotBoundaryPositiveIrrationalHomeomorph c).property
      have heq := (ENNReal.ofReal_eq_ofReal_iff hx.2.le
        (show 0 ≤ (q : ℝ) by exact_mod_cast hq.le)).mp he
      exact False.elim (hx.1.ne_rat q heq)
    · apply hfiber b hS
      simpa only [mediantIntervalLimit_eq_sternBrocotMediantLimitValue] using hb

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Composing with the
    continued-fraction homeomorphism from §{sec:simple-continued-fractions} shows that $\MediantLimitMap$ restricts to a
    homeomorphism $S \to \SetDifference{\RestrictedSet{\R}{>0}}{\QQ}$.
-/
/-- The existing run-length homeomorphism has the geometric limit as its value. -/
theorem mediantIntervalLimit_restrict_homeomorphism :
    ∃ h : cantorNonEventuallyConstantBranches ≃ₜ {x : ℝ // Irrational x ∧ 0 < x},
      ∀ b, mediantIntervalLimit b.1 = ENNReal.ofReal (h b).1 :=
  ⟨sternBrocotBoundaryPositiveIrrationalHomeomorph, mediantIntervalLimit_positiveIrrational⟩

end PolishSpaceBook
