module

public import PolishSpaceBook.ConcreteCantorBaireModels
public import Mathlib.Topology.Instances.Irrational

@[expose] public section

namespace PolishSpaceBook

/-- The frame after the initial right run and `n` positive alternating runs. -/
def continuedFractionRunFrame (a₀ : ℕ) (a : ℕ → ℕ) : ℕ → MediantFrame
  | 0 => MediantFrame.root.rightRun a₀
  | n + 1 => if Even n then (continuedFractionRunFrame a₀ a n).leftRun (a (n + 1))
      else (continuedFractionRunFrame a₀ a n).rightRun (a (n + 1))

/-- Numerators and denominators, including the integer-part translation. -/
def continuedFractionColumn (a₀ : ℕ) (a : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | 1 => (a₀, 1)
  | n + 2 =>
      (a (n + 1) * (continuedFractionColumn a₀ a (n + 1)).1 +
        (continuedFractionColumn a₀ a n).1,
       a (n + 1) * (continuedFractionColumn a₀ a (n + 1)).2 +
        (continuedFractionColumn a₀ a n).2)

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Use the convergent recurrence $(*)$ for $s$, and put $P_j=a_0q_j+p_j$.
    Before appending $D_{n+1}$, the endpoints of $J_{v_n}$, in increasing order, are
    $$
    \begin{cases}
    (P_{n+1}/q_{n+1},\;P_n/q_n),&n\text{ even},\\
    (P_n/q_n,\;P_{n+1}/q_{n+1}),&n\text{ odd}.
    \end{cases}
    $$
    For $n=0$ these are $a_0/1$ and $1/0$. To pass from $n$ to $n+1$, repeat the next direction $a_{n+1}$ times.
    The endpoint that changes becomes
    $$(P_{n+2},q_{n+2})=a_{n+1}(P_{n+1},q_{n+1})+(P_n,q_n),$$
    while the other endpoint stays fixed. This proves the endpoint formula by induction.
-/
/-- Run endpoints are the two successive convergent columns, in parity order. -/
theorem continuedFractionRunFrame_columns (a₀ : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    let f := continuedFractionRunFrame a₀ a n
    ((f.a, f.b), (f.c, f.d)) =
      if Even n then (continuedFractionColumn a₀ a (n + 1), continuedFractionColumn a₀ a n)
      else (continuedFractionColumn a₀ a n, continuedFractionColumn a₀ a (n + 1)) := by
  induction n with
  | zero => simp [continuedFractionRunFrame, continuedFractionColumn,
      MediantFrame.root, MediantFrame.rightRun]
  | succ n ih =>
    dsimp only at ih ⊢
    by_cases hn : Even n
    · have hn' : ¬ Even (n + 1) := by
        intro h
        rcases hn with ⟨k, hk⟩
        rcases h with ⟨l, hl⟩
        omega
      simp only [hn, ite_eq_left] at ih
      have ha := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1) ih
      have hb := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.2) ih
      have hc := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1) ih
      have hd := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.2) ih
      simp only [continuedFractionRunFrame, hn, ite_eq_left, hn', ite_false,
        MediantFrame.leftRun, continuedFractionColumn, Prod.mk.injEq] at *
      aesop (add simp [Nat.add_comm])
    · have hn' : Even (n + 1) := by
        rcases Nat.not_even_iff_odd.mp hn with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      simp only [hn, ite_false] at ih
      have ha := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1) ih
      have hb := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.2) ih
      have hc := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1) ih
      have hd := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.2) ih
      simp only [continuedFractionRunFrame, hn, ite_false, hn', ite_true,
        MediantFrame.rightRun, continuedFractionColumn, Prod.mk.injEq] at *
      aesop (add simp [Nat.add_comm])

/-- The natural-number columns agree with the book's integer continuants. -/
theorem continuedFractionColumn_eq_convergents (a₀ : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    (((continuedFractionColumn a₀ a n).1 : ℤ), ((continuedFractionColumn a₀ a n).2 : ℤ)) =
      ((a₀ : ℤ) * simpleCFDen (fun k => (a k : ℤ)) n +
        simpleCFNum (fun k => (a k : ℤ)) n,
       simpleCFDen (fun k => (a k : ℤ)) n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuedFractionColumn, simpleCFNum, simpleCFDen]
  | one => simp [continuedFractionColumn, simpleCFNum, simpleCFDen]
  | more n ih ih' =>
    have hp := congrArg Prod.fst ih
    have hq := congrArg Prod.snd ih
    have hp' := congrArg Prod.fst ih'
    have hq' := congrArg Prod.snd ih'
    dsimp only at hp hq hp' hq'
    simp only [continuedFractionColumn, Nat.cast_add, Nat.cast_mul,
      simpleCFNum_succ_succ, simpleCFDen_succ_succ, hp, hq, hp', hq']
    congr 1; ring


/-- Append the first opposite letter, as in the book's completed-run cylinders. -/
def continuedFractionCompletedFrame (a₀ : ℕ) (a : ℕ → ℕ) (n : ℕ) : MediantFrame :=
  if Even n then (continuedFractionRunFrame a₀ a n).left
  else (continuedFractionRunFrame a₀ a n).right

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Appending the single opposite letter $D_{n+1}$ to $v_n$ keeps $P_{n+1}/q_{n+1}$ and replaces the other endpoint
    by $(P_{n+1}+P_n)/(q_{n+1}+q_n)$. These are exactly the two endpoints of the continued-fraction cylinder computed
    in §{sec:stern-brocot-cylinder-geometry}. The same formula for the empty prefix gives $[a_0,a_0+1]$.
-/
/-- The completed-run interval has one convergent endpoint and one mediant endpoint. -/
theorem continuedFractionCompletedFrame_columns (a₀ : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    let f := continuedFractionCompletedFrame a₀ a n
    let p := continuedFractionColumn a₀ a (n + 1)
    let q := continuedFractionColumn a₀ a n
    ((f.a, f.b), (f.c, f.d)) =
      if Even n then (p, (p.1 + q.1, p.2 + q.2))
      else ((p.1 + q.1, p.2 + q.2), p) := by
  have h := continuedFractionRunFrame_columns a₀ a n
  dsimp only at h ⊢
  by_cases hn : Even n
  · simp only [hn, ite_eq_left] at h
    have ha := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1) h
    have hb := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.2) h
    have hc := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1) h
    have hd := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.2) h
    dsimp only at ha hb hc hd
    simp [continuedFractionCompletedFrame, hn, MediantFrame.left, ha, hb, hc, hd]
  · simp only [hn, ite_false] at h
    have ha := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1) h
    have hb := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.2) h
    have hc := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1) h
    have hd := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.2) h
    dsimp only at ha hb hc hd
    simp [continuedFractionCompletedFrame, hn, MediantFrame.right, ha, hb, hc, hd,
      Nat.add_comm]

/-- Reading a finite binary word from a frame. -/
def readMediantWord (f : MediantFrame) (w : List Bool) : MediantFrame :=
  w.foldl MediantFrame.child f

@[simp] theorem readMediantWord_append (f : MediantFrame) (v w : List Bool) :
    readMediantWord f (v ++ w) = readMediantWord (readMediantWord f v) w := by
  simp [readMediantWord]

theorem readMediantWord_replicate (f : MediantFrame) (k : ℕ) (b : Bool) :
    readMediantWord f (List.replicate k b) =
      if b then f.rightRun k else f.leftRun k := by
  have h : readMediantWord f (List.replicate k b) =
      (fun g : MediantFrame => g.child b)^[k] f := by
    induction k generalizing f with
    | zero => rfl
    | succ k ih =>
      change readMediantWord (f.child b) (List.replicate k b) = _
      rw [ih, Function.iterate_succ_apply]
  rw [h]
  cases b <;> simp [MediantFrame.child, MediantFrame.iterate_left, MediantFrame.iterate_right]

/-- The actual finite L/R word ending after the `n`-th partial quotient. -/
def continuedFractionRunWord (a₀ : ℕ) (a : ℕ → ℕ) : ℕ → List Bool
  | 0 => List.replicate a₀ true
  | n + 1 => continuedFractionRunWord a₀ a n ++ List.replicate (a (n + 1)) (!decide (Even n))

theorem readMediantWord_runWord (a₀ : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    readMediantWord MediantFrame.root (continuedFractionRunWord a₀ a n) =
      continuedFractionRunFrame a₀ a n := by
  induction n with
  | zero => simp [continuedFractionRunWord, readMediantWord_replicate, continuedFractionRunFrame]
  | succ n ih =>
    rw [continuedFractionRunWord, readMediantWord_append, ih, readMediantWord_replicate]
    by_cases hn : Even n <;> simp [continuedFractionRunFrame, hn]

/-- Completing a run reads exactly one more letter of the mediant construction. -/
theorem readMediantWord_completedRun (a₀ : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    readMediantWord MediantFrame.root
      (continuedFractionRunWord a₀ a n ++ [!decide (Even n)]) =
        continuedFractionCompletedFrame a₀ a n := by
  rw [readMediantWord_append, readMediantWord_runWord]
  by_cases hn : Even n <;>
    simp [readMediantWord, continuedFractionCompletedFrame, MediantFrame.child, hn]


theorem mediantBranchFrame_eq_readMediantWord {z : cantor_space} {w : finseq Bool}
    (h : z ∈ cyl w) :
    mediantBranchFrame z w.length = readMediantWord MediantFrame.root w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih =>
    have hh := (mem_cyl_concat_iff (s := w) (t := [b])).mp h
    have hb : z w.length = b := by
      simpa using prefixOfSeq_singleton.mp hh.2
    simp only [List.length_append, List.length_singleton, mediantBranchFrame,
      ih hh.1, hb, readMediantWord_append]
    rfl

theorem continuedFractionRunWord_length_ge (a₀ : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, 0 < k → 0 < a k) (n : ℕ) :
    n ≤ (continuedFractionRunWord a₀ a n).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    have := ha (n + 1) (by omega)
    simp only [continuedFractionRunWord, List.length_append, List.length_replicate]
    omega

/-- Along a represented infinite run word, each convergent column is an endpoint
of the actual mediant interval. -/
theorem continuedFractionColumn_mem_branchInterval
    (z : cantor_space) (a₀ : ℕ) (a : ℕ → ℕ)
    (hz : ∀ n, z ∈ cyl (continuedFractionRunWord a₀ a n)) (n : ℕ) :
    let p := continuedFractionColumn a₀ a (n + 1)
    (p.1 : ℝ) / (p.1 + p.2) ∈
      (mediantBranchFrame z (continuedFractionRunWord a₀ a n).length).interval := by
  rw [mediantBranchFrame_eq_readMediantWord (hz n), readMediantWord_runWord]
  have h := continuedFractionRunFrame_columns a₀ a n
  dsimp only at h ⊢
  by_cases hn : Even n
  · simp only [hn, ite_eq_left] at h
    have ha := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1) h
    have hb := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.2) h
    dsimp only at ha hb
    have he : (continuedFractionRunFrame a₀ a n).lower =
        ((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) /
          ((continuedFractionColumn a₀ a (n + 1)).1 + (continuedFractionColumn a₀ a (n + 1)).2) := by
      simp [MediantFrame.lower, ha, hb]
    rw [← he]
    exact ⟨le_rfl, (continuedFractionRunFrame a₀ a n).lower_lt_upper.le⟩
  · simp only [hn, ite_false] at h
    have hc := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1) h
    have hd := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.2) h
    dsimp only at hc hd
    have he : (continuedFractionRunFrame a₀ a n).upper =
        ((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) /
          ((continuedFractionColumn a₀ a (n + 1)).1 + (continuedFractionColumn a₀ a (n + 1)).2) := by
      simp [MediantFrame.upper, hc, hd]
    rw [← he]
    exact ⟨(continuedFractionRunFrame a₀ a n).lower_lt_upper.le, le_rfl⟩


open scoped Topology
open Filter Set

theorem continuedFractionColumn_compactified_convergent (a₀ : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, 0 < k → 0 < a k) (n : ℕ) :
    let p := continuedFractionColumn a₀ a (n + 1)
    (p.1 : ℝ) / (p.1 + p.2) =
      (ENNReal.orderIsoUnitIntervalBirational
        (ENNReal.ofReal ((a₀ : ℝ) + (simpleCFConvergent (fun k => (a k : ℤ)) n : ℝ))) : ℝ) := by
  have hpos : SimpleCFPositivePartials (fun k => (a k : ℤ)) := by
    intro k
    change (1 : ℤ) ≤ (a (k + 1) : ℤ)
    exact_mod_cast (show 1 ≤ a (k + 1) from ha (k + 1) (by omega))
  have hc := continuedFractionColumn_eq_convergents a₀ a (n + 1)
  have hp := congrArg Prod.fst hc
  have hq := congrArg Prod.snd hc
  dsimp only at hp hq ⊢
  have hd : 0 < (continuedFractionColumn a₀ a (n + 1)).2 := by
    have := simpleCFDen_pos_of_positive hpos n
    rw [← hq] at this
    exact_mod_cast this
  have hpR : ((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) =
      (a₀ : ℝ) * simpleCFDen (fun k => (a k : ℤ)) (n + 1) +
        simpleCFNum (fun k => (a k : ℤ)) (n + 1) := by exact_mod_cast hp
  have hqR : ((continuedFractionColumn a₀ a (n + 1)).2 : ℝ) =
      simpleCFDen (fun k => (a k : ℤ)) (n + 1) := by exact_mod_cast hq
  have hdR : (0 : ℝ) < simpleCFDen (fun k => (a k : ℤ)) (n + 1) := by
    exact_mod_cast simpleCFDen_pos_of_positive hpos n
  have hv : ((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) /
      (continuedFractionColumn a₀ a (n + 1)).2 =
        (a₀ : ℝ) + (simpleCFConvergent (fun k => (a k : ℤ)) n : ℝ) := by
    rw [hpR, hqR]
    simp only [simpleCFConvergent, Rat.cast_div, Rat.cast_intCast]
    field_simp
  rw [← hv, ENNReal.ofReal_div_of_pos (by exact_mod_cast hd)]
  simp only [ENNReal.ofReal_natCast]
  exact (mediantCompactify_fraction _ _ (by omega)).symm

/-- The geometric mediant limit of an infinite continued-fraction run word is
its continued-fraction value. The run-word hypothesis states the displayed
infinite concatenation in the book using all its finite prefixes. -/
theorem mediantIntervalLimit_of_continuedFractionRuns
    (z : cantor_space) (a₀ : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, 0 < k → 0 < a k)
    (hz : ∀ n, z ∈ cyl (continuedFractionRunWord a₀ a n))
    {β : ℝ}
    (hβ : Tendsto (fun n => (simpleCFConvergent (fun k => (a k : ℤ)) n : ℝ))
      atTop (𝓝 β)) :
    mediantIntervalLimit z = ENNReal.ofReal ((a₀ : ℝ) + β) := by
  have ht := (continuous_subtype_val.tendsto
      (ENNReal.orderIsoUnitIntervalBirational (ENNReal.ofReal ((a₀ : ℝ) + β)))).comp
    (ENNReal.orderIsoUnitIntervalBirational.continuous.tendsto _ |>.comp
      (ENNReal.continuous_ofReal.tendsto _ |>.comp (tendsto_const_nhds.add hβ)))
  have hc : Tendsto (fun n =>
      (((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) /
        ((continuedFractionColumn a₀ a (n + 1)).1 + (continuedFractionColumn a₀ a (n + 1)).2)))
      atTop (𝓝 (ENNReal.orderIsoUnitIntervalBirational (ENNReal.ofReal ((a₀ : ℝ) + β)) : ℝ)) := by
    convert ht using 1
    funext n
    exact continuedFractionColumn_compactified_convergent a₀ a ha n
  apply (mediantIntervalLimit_eq_iff z _).mpr
  intro N
  rw [MediantFrame.mem_extendedInterval_iff]
  apply isClosed_Icc.mem_of_tendsto hc
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  exact mediantBranchFrame_intervals_antitone z
    (hn.trans (continuedFractionRunWord_length_ge a₀ a ha n))
    (continuedFractionColumn_mem_branchInterval z a₀ a hz n)

open Set Filter
open scoped Topology

/-- The finite tail expression recovers exactly the prescribed algorithmic
partial quotients, and its remaining fractional tail is the reciprocal input. -/
theorem simpleCFTailMap_algorithm_prefix (a₀ : ℤ) {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {t : ℝ} (ht : 1 < t) :
    let x := (a₀ : ℝ) + simpleCFTailMap a n t
    simpleCFIntegerPart x = a₀ ∧
      (∀ k, 0 < k → k ≤ n → simpleCFAlgorithmPartials x k = a k) ∧
      simpleCFFractionalRemainder x n = t⁻¹ := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hi0 : 0 < t⁻¹ := inv_pos.mpr htpos
  have hi1 : t⁻¹ < 1 := (inv_lt_one₀ htpos).mpr ht
  induction n generalizing t with
  | zero =>
      simp only [simpleCFTailMap, simpleCFNum, simpleCFDen]
      simp only [Int.cast_zero, Int.cast_one, mul_zero, mul_one, add_zero, zero_add,
        one_div]
      refine ⟨?_, ?_, ?_⟩
      · unfold simpleCFIntegerPart
        rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨hi0.le, hi1⟩, add_zero]
      · intro k hk hkn
        omega
      · simp only [simpleCFFractionalRemainder, Int.fract_intCast_add]
        exact Int.fract_eq_self.mpr ⟨hi0.le, hi1⟩
  | succ n ih =>
      let u : ℝ := (a (n + 1) : ℝ) + t⁻¹
      have ha1 : (1 : ℝ) ≤ (a (n + 1) : ℝ) := by exact_mod_cast ha n
      have hu : 1 < u := by dsimp [u]; linarith
      have hrec : simpleCFTailMap a (n + 1) t = simpleCFTailMap a n u := by
        simpa [u, one_div] using (simpleCFTailMap_succ_eq (a := a) (n := n)
          (ne_of_gt htpos)).symm
      rw [hrec]
      rcases ih hu (lt_trans zero_lt_one hu) (inv_pos.mpr (lt_trans zero_lt_one hu))
        ((inv_lt_one₀ (lt_trans zero_lt_one hu)).mpr hu) with ⟨hfloor, hprefix, hrem⟩
      have hufloor : ⌊u⌋ = a (n + 1) := by
        dsimp [u]
        rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨hi0.le, hi1⟩, add_zero]
      refine ⟨hfloor, ?_, ?_⟩
      · intro k hk hkn
        by_cases hle : k ≤ n
        · exact hprefix k hk hle
        · have : k = n + 1 := by omega
          subst k
          simp only [simpleCFAlgorithmPartials, hrem, inv_inv]
          exact hufloor
      · simp only [simpleCFFractionalRemainder, hrem, inv_inv]
        dsimp [u]
        rw [Int.fract_intCast_add]
        exact Int.fract_eq_self.mpr ⟨hi0.le, hi1⟩

/-- The inverse coordinate cylinder is precisely the image of irrational complete
quotients greater than one, including the empty prefix. -/
theorem simpleCFFractionalCylinder_eq_tail_image (a₀ : ℤ) (pref : finseq positiveNat) :
    Subtype.val '' simpleCFFractionalCylinder a₀ pref =
      (fun t : ℝ => (a₀ : ℝ) +
        simpleCFTailMap (positiveNatSeqPartials (extendFinseq pref)) pref.length t) ''
          {t : ℝ | Irrational t ∧ 1 < t} := by
  let a := positiveNatSeqPartials (extendFinseq pref)
  have ha : SimpleCFPositivePartials a := positiveNatSeqPartials_positive _
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    let b := simpleCFAlgorithmPartials y.1
    let α := simpleCFFractionalRemainder y.1
    have hb : SimpleCFPositivePartials b :=
      simpleCFAlgorithmPartialsPositive_of_irrational y.1 y.2.1
    have hα := simpleCFFractionalRemainder_irrational_unitInterval y.1 y.2.1
    have heq : ∀ k, k ≤ pref.length → b k = a k := by
      have h := positiveNatSeqPartials_eq_on_le_of_mem_same_cyl
        (show simpleCFIrrationalTail ⟨y.1, y.2.1⟩ ∈ cyl pref from hy)
        (extendFinseq_mem_cyl pref)
      simpa [b, a, positiveNatSeqPartials_simpleCFIrrationalTail] using h
    have htail := SimpleCFTailFormulaClaim
      (simpleCFAlgorithmCompleteQuotientRelation_of_irrational y.1 y.2.1)
      (fun k => add_pos_of_nonneg_of_pos
        (by exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) (hb k)))
        (hα (k + 1)).2.1) pref.length
    have hfloor : simpleCFIntegerPart y.1 = a₀ := by
      rw [simpleCFIntegerPart, Int.floor_eq_iff]
      exact ⟨y.2.2.1.le, y.2.2.2⟩
    refine ⟨(α pref.length)⁻¹, ⟨(hα pref.length).1.inv, ?_⟩, ?_⟩
    · exact (one_lt_inv₀ (hα pref.length).2.1).mpr (hα pref.length).2.2
    · have hval : y.1 = (a₀ : ℝ) + α 0 := by
        have hf : ⌊y.1⌋ = a₀ := hfloor
        change y.1 = (a₀ : ℝ) + Int.fract y.1
        calc
          y.1 = Int.fract y.1 + (⌊y.1⌋ : ℝ) := (Int.fract_add_floor y.1).symm
          _ = (a₀ : ℝ) + Int.fract y.1 := by rw [hf]; ring
      have hnum := simpleCFNum_eq_of_eq_on_le heq (Nat.le_refl (pref.length + 1))
      have hnum' := simpleCFNum_eq_of_eq_on_le heq (Nat.le_succ pref.length)
      have hden := simpleCFDen_eq_of_eq_on_le heq (Nat.le_refl (pref.length + 1))
      have hden' := simpleCFDen_eq_of_eq_on_le heq (Nat.le_succ pref.length)
      change (a₀ : ℝ) + simpleCFTailMap a pref.length (α pref.length)⁻¹ = y.1
      rw [hval]
      congr 1
      change α 0 = simpleCFCompleteQuotientValue b pref.length (α pref.length) at htail
      rw [htail]
      simp only [simpleCFTailMap, simpleCFCompleteQuotientValue,
        hnum, hnum', hden, hden']
      have hne : α pref.length ≠ 0 := ne_of_gt (hα pref.length).2.1
      field_simp [hne]
  · rintro x ⟨t, ⟨htirr, ht⟩, rfl⟩
    have hprefix := simpleCFTailMap_algorithm_prefix a₀ ha pref.length ht
    have hxirr : Irrational ((a₀ : ℝ) + simpleCFTailMap a pref.length t) :=
      (simpleCFTailMap_irrational_of_irrational ha pref.length
        (lt_trans zero_lt_one ht) htirr).intCast_add a₀
    have hfloor := hprefix.1
    have hbounds := Int.floor_eq_iff.mp hfloor
    let y : simpleCFFractionalInterval a₀ :=
      ⟨(a₀ : ℝ) + simpleCFTailMap a pref.length t,
        hxirr, lt_of_le_of_ne hbounds.1 (Ne.symm (hxirr.ne_int a₀)), hbounds.2⟩
    refine ⟨y, ?_, rfl⟩
    rw [mem_simpleCFFractionalCylinder_iff]
    intro i hi
    have hh := hprefix.2.1 (i + 1) (by omega) (by omega)
    have hcanon := positiveNatSeqPartials_simpleCFIrrationalTail ⟨y.1, y.2.1⟩
    have hnat : simpleCFIrrationalTail ⟨y.1, y.2.1⟩ i = extendFinseq pref i := by
      apply Subtype.ext
      have hh' := congrFun hcanon (i + 1)
      change ((simpleCFIrrationalTail ⟨y.1, y.2.1⟩ i : ℕ) : ℤ) = _ at hh'
      have : ((simpleCFIrrationalTail ⟨y.1, y.2.1⟩ i : ℕ) : ℤ) =
          (((extendFinseq pref : ℕ → positiveNat) i : ℕ) : ℤ) := hh'.trans hh
      exact_mod_cast this
    exact hnat.trans (extendFinseq_mem_cyl pref i hi)

/-- Removing rational points does not change the closure of a nonempty open interval. -/
theorem closure_irrational_Ioo {l u : ℝ} (hlu : l < u) :
    closure {x : ℝ | Irrational x ∧ x ∈ Ioo l u} = Icc l u := by
  change closure ({x : ℝ | Irrational x} ∩ Ioo l u) = _
  rw [inter_comm]
  apply Set.Subset.antisymm
  · exact (closure_mono inter_subset_left).trans_eq (closure_Ioo hlu.ne)
  · have h : Ioo l u ⊆ closure (Ioo l u ∩ {x : ℝ | Irrational x}) := by
      simpa only [dense_irrational.closure_eq, inter_univ] using
        (isOpen_Ioo.inter_closure (t := {x : ℝ | Irrational x}))
    simpa only [closure_Ioo hlu.ne, closure_closure] using closure_mono h

/-- The coordinate-cylinder closure has the two continued-fraction endpoints,
with the parity orientation used in the book. -/
theorem closure_simpleCFFractionalCylinder (a₀ : ℤ) (pref : finseq positiveNat) :
    let a := positiveNatSeqPartials (extendFinseq pref)
    closure (Subtype.val '' simpleCFFractionalCylinder a₀ pref) =
      if Even pref.length then
        Icc ((a₀ : ℝ) + simpleCFEndpoint a pref.length)
          ((a₀ : ℝ) + simpleCFAdjacentEndpoint a pref.length)
      else
        Icc ((a₀ : ℝ) + simpleCFAdjacentEndpoint a pref.length)
          ((a₀ : ℝ) + simpleCFEndpoint a pref.length) := by
  dsimp only
  rw [simpleCFFractionalCylinder_eq_tail_image,
    simpleCFTailImageInterval_eq_of_positive a₀ (positiveNatSeqPartials_positive _)]
  have h := simpleCFTailMap_mem_interval_of_gt_one
    (positiveNatSeqPartials_positive (extendFinseq pref)) a₀ pref.length
    (x := 2) (by norm_num)
  split_ifs with hn
  · simp only [hn, ite_eq_left] at h ⊢
    exact closure_irrational_Ioo (h.1.trans h.2)
  · simp only [hn] at h ⊢
    exact closure_irrational_Ioo (h.1.trans h.2)

/-- Cast the run columns to the real convergent recurrence. -/
theorem continuedFractionColumn_real_coordinates (a₀ : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    let p := continuedFractionColumn a₀ a k
    (p.1 : ℝ) = (a₀ : ℝ) * (simpleCFDen (fun j => (a j : ℤ)) k : ℝ) +
      (simpleCFNum (fun j => (a j : ℤ)) k : ℝ) ∧
    (p.2 : ℝ) = (simpleCFDen (fun j => (a j : ℤ)) k : ℝ) := by
  have h := continuedFractionColumn_eq_convergents a₀ a k
  have hp := congrArg Prod.fst h
  have hq := congrArg Prod.snd h
  constructor <;> dsimp only at hp hq ⊢
  · exact_mod_cast hp
  · exact_mod_cast hq

/-- The real interval after the first opposite letter has the cylinder's endpoints. -/
theorem continuedFractionCompletedFrame_real_interval (a₀ : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, 0 < k → 0 < a k) (n : ℕ) :
    let f := continuedFractionCompletedFrame a₀ a n
    Icc ((f.a : ℝ) / f.b) ((f.c : ℝ) / f.d) =
      if Even n then
        Icc ((a₀ : ℝ) + simpleCFEndpoint (fun k => (a k : ℤ)) n)
          ((a₀ : ℝ) + simpleCFAdjacentEndpoint (fun k => (a k : ℤ)) n)
      else
        Icc ((a₀ : ℝ) + simpleCFAdjacentEndpoint (fun k => (a k : ℤ)) n)
          ((a₀ : ℝ) + simpleCFEndpoint (fun k => (a k : ℤ)) n) := by
  let b : ℕ → ℤ := fun k => (a k : ℤ)
  have hb : SimpleCFPositivePartials b := by
    intro k
    change (1 : ℤ) ≤ (a (k + 1) : ℤ)
    exact_mod_cast (show 1 ≤ a (k + 1) from ha (k + 1) (by omega))
  have hq : (simpleCFDen b (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (simpleCFDen_pos_of_positive hb n))
  have hsum : ((simpleCFDen b (n + 1) : ℝ) + (simpleCFDen b n : ℝ)) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg
      (by exact_mod_cast simpleCFDen_pos_of_positive hb n)
      (by exact_mod_cast simpleCFDen_nonneg_of_positive hb n))
  have hp := continuedFractionColumn_real_coordinates a₀ a (n + 1)
  have hp' := continuedFractionColumn_real_coordinates a₀ a n
  dsimp only at hp hp'
  have hval : ((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) /
      (continuedFractionColumn a₀ a (n + 1)).2 =
        (a₀ : ℝ) + simpleCFEndpoint b n := by
    rw [hp.1, hp.2, simpleCFEndpoint_eq_div]
    dsimp [b] at hq ⊢
    field_simp [hq]
  have hadj : (((continuedFractionColumn a₀ a (n + 1)).1 : ℝ) +
      (continuedFractionColumn a₀ a n).1) /
      (((continuedFractionColumn a₀ a (n + 1)).2 : ℝ) +
        (continuedFractionColumn a₀ a n).2) =
      (a₀ : ℝ) + simpleCFAdjacentEndpoint b n := by
    rw [hp.1, hp.2, hp'.1, hp'.2]
    simp only [simpleCFAdjacentEndpoint, Int.cast_add]
    dsimp [b] at hsum ⊢
    field_simp [hsum]
    ring
  have hcols := continuedFractionCompletedFrame_columns a₀ a n
  dsimp only at hcols ⊢
  have h := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
    Icc ((p.1.1 : ℝ) / p.1.2) ((p.2.1 : ℝ) / p.2.2)) hcols
  dsimp only at h
  by_cases hn : Even n
  · simpa only [hn, ite_eq_left, Nat.cast_add, hval, hadj] using h
  · simpa only [hn, ite_false, Nat.cast_add, hval, hadj] using h

/-- Both endpoints after a completed run are finite real quotients. -/
theorem continuedFractionCompletedFrame_den_pos (a₀ : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, 0 < k → 0 < a k) (n : ℕ) :
    let f := continuedFractionCompletedFrame a₀ a n
    0 < f.b ∧ 0 < f.d := by
  have hb : SimpleCFPositivePartials (fun k => (a k : ℤ)) := by
    intro k
    change (1 : ℤ) ≤ (a (k + 1) : ℤ)
    exact_mod_cast (show 1 ≤ a (k + 1) from ha (k + 1) (by omega))
  have hp := (continuedFractionColumn_real_coordinates a₀ a (n + 1)).2
  have hpos : 0 < (continuedFractionColumn a₀ a (n + 1)).2 := by
    have : (0 : ℝ) < ((continuedFractionColumn a₀ a (n + 1)).2 : ℝ) := by
      rw [hp]
      exact_mod_cast simpleCFDen_pos_of_positive hb n
    exact_mod_cast this
  have hcols := continuedFractionCompletedFrame_columns a₀ a n
  have h := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (p.1.2, p.2.2)) hcols
  dsimp only at h ⊢
  split_ifs at h with hn
  · have := congrArg Prod.fst h
    have := congrArg Prod.snd h
    dsimp only at *
    omega
  · have := congrArg Prod.fst h
    have := congrArg Prod.snd h
    dsimp only at *
    omega

/-- Positive run lengths extending a finite positive-integer prefix. -/
noncomputable def completedRunPartials (pref : finseq positiveNat) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (extendFinseq pref : ℕ → positiveNat) k

theorem completedRunPartials_cast (pref : finseq positiveNat) :
    (fun k => (completedRunPartials pref k : ℤ)) =
      positiveNatSeqPartials (extendFinseq pref) := by
  funext k
  cases k <;> rfl

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: statement
  kind: lemma
  title: Completed runs and continued-fraction cylinders
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Taking the closure fills the rational points and both endpoints, proving the equality.
-/
/-- Full closure equality for the actual finite word and the inverse coordinate
cylinder, not only an equality of formal endpoint recurrences. -/
theorem completedRun_cylinder_closure (a₀ : ℕ) (pref : finseq positiveNat) :
    let a := completedRunPartials pref
    let f := readMediantWord MediantFrame.root
      (continuedFractionRunWord a₀ a pref.length ++ [!decide (Even pref.length)])
    Icc ((f.a : ℝ) / f.b) ((f.c : ℝ) / f.d) =
      closure (Subtype.val '' simpleCFFractionalCylinder (a₀ : ℤ) pref) := by
  dsimp only
  rw [readMediantWord_completedRun,
    continuedFractionCompletedFrame_real_interval a₀ (completedRunPartials pref) ?_,
    completedRunPartials_cast, closure_simpleCFFractionalCylinder]
  · simp only [Int.cast_natCast]
  · intro k hk
    cases k with
    | zero => omega
    | succ k => exact (extendFinseq pref : ℕ → positiveNat) k |>.property

end PolishSpaceBook


