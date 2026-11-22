module

public import PolishSpaceBook.WadgeStrategyReduction

@[expose] public section

/-!
# Playing a continuous map with passes

At a finite input prefix, emit the next coordinate exactly when it is constant
on that cylinder. Continuity ensures eventual emission of every coordinate.
The strategy reads only the finite input history; its previous responses are
reconstructed by the same rule.
-/
noncomputable section
namespace PolishSpaceBook.WadgeGame
open Set Function Filter Topology
open scoped Classical

abbrev Baire := ℕ → ℕ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For (1, $\Leftarrow$), suppose $A=f^{-1}(B)$ with $f$ continuous. For a finite input word $s$, let
    $\widehat{s}$ extend $s$ by zeros, and write
    $$K_f(s,k)\quad\Longleftrightarrow\quad
    \forall z\in\cyl{s}\quad f(z)(k)=f(\widehat{s})(k).$$
    This condition says that the next requested value is already determined on the whole cylinder.
    Use code $0$ for a pass and code $m+1$ for a genuine move $m$. After I has supplied $x(0),\ldots,x(n)$,
    put $s_n:=\restrict{x}{n+1}$. Start with $k_0:=0$ and apply the rule
    $$
    (c_n,k_{n+1}):=
    \begin{cases}
    (f(\widehat{s_n})(k_n)+1,\ k_n+1),&K_f(s_n,k_n),\\
    (0,\ k_n),&\text{otherwise}.
    \end{cases}
    $$
    Here $c_n$ is II's next coded move, and $k_n$ is the number of genuine moves already made. The count and all
    previous responses can be reconstructed from the finite input word, so this is a strategy on finite histories.
    Whenever a genuine move is made, its decoded value is $f(x)(k_n)$, since $x\in\cyl{s_n}$.

    It remains to prove that the strategy produces every coordinate. For fixed $x$ and $k$, continuity of the
    $k$-th coordinate of $f$ gives a cylinder containing $x$ on which that coordinate is constant.
    Every sufficiently long input prefix determines a subcylinder of it, so $K_f(s_n,k)$ holds for all sufficiently
    large $n$. The counts $k_n$ are nondecreasing. If at least $k$ values have been emitted, then either the next
    one has already been emitted or the count is still $k$; in the latter case it increases as soon as a sufficiently
    long prefix has been read. Induction on $k$ proves that arbitrarily many values are emitted.
    Thus the play has infinitely many genuine moves, its output is exactly $f(x)$, and $A=f^{-1}(B)$ makes the
    strategy winning for II.
-/
/-- The next requested coordinate is already fixed on this input cylinder. -/
def Known (f : Baire → Baire) (s : List ℕ) (k : ℕ) : Prop :=
  ∀ z ∈ cyl s, f z k = f (extendFinseq s) k

lemma prefix_eq_of_agree {x y : Baire} {n : ℕ} (h : ∀ i < n, x i = y i) : seqPrefix x n = seqPrefix y n := by
  apply congrArg List.ofFn
  funext i
  exact h i.val i.isLt

lemma known_eventually {f : Baire → Baire} (hf : Continuous f) (x : Baire) (k : ℕ) :
    ∃ N, ∀ n ≥ N, Known f (seqPrefix x n) k := by
  let U := {z : Baire | f z k = f x k}
  have hU : IsOpen U := (isOpen_discrete ({f x k} : Set ℕ)).preimage ((continuous_apply k).comp hf)
  obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open (show x ∈ U from rfl) hU
  refine ⟨s.length, ?_⟩
  intro n hn
  have hsub : cyl (seqPrefix x n) ⊆ cyl s := by
    intro z hz i hi
    have hz' := hz i (by simp; omega)
    exact (hz'.trans (seqPrefix_get x _)).trans (hxs i hi)
  intro z hz
  exact (hsU (hsub hz)).trans (hsU (hsub (extendFinseq_mem_cyl _))).symm

/-- Number of coordinates emitted after reading `n` input moves. -/
def sent (f : Baire → Baire) (x : Baire) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if Known f (seqPrefix x (n + 1)) (sent f x n) then sent f x n + 1 else sent f x n

/-- Zero is a pass; a positive code is the determined output plus one. -/
def emission (f : Baire → Baire) (x : Baire) (n : ℕ) : ℕ :=
  if Known f (seqPrefix x (n + 1)) (sent f x n) then
    f (extendFinseq (seqPrefix x (n + 1))) (sent f x n) + 1 else 0

lemma sent_mono (f : Baire → Baire) (x : Baire) : Monotone (sent f x) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [sent]
  split_ifs <;> omega

lemma sent_step (f : Baire → Baire) (x : Baire) (n : ℕ) :
    sent f x (n + 1) = sent f x n + if emission f x n = 0 then 0 else 1 := by
  by_cases h : Known f (seqPrefix x (n + 1)) (sent f x n)
  · simp [sent, emission, h]
  · simp [sent, emission, h]

lemma sent_congr (f : Baire → Baire) {x y : Baire} {n : ℕ}
    (h : ∀ i < n, x i = y i) : sent f x n = sent f y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (fun i hi => h i (by omega))
    simp only [sent, hprev, prefix_eq_of_agree h]

lemma emission_congr (f : Baire → Baire) {x y : Baire} {n : ℕ}
    (h : ∀ i < n + 1, x i = y i) : emission f x n = emission f y n := by
  simp only [emission, sent_congr f (fun i (hi : i < n) => h i (by omega)), prefix_eq_of_agree h]

lemma sent_unbounded {f : Baire → Baire} (hf : Continuous f) (x : Baire) (k : ℕ) :
    ∃ n, k ≤ sent f x n := by
  induction k with
  | zero => exact ⟨0, le_rfl⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨N, hN⟩ := known_eventually hf x k
    let m := max n N
    have hkm : k ≤ sent f x m := hn.trans (sent_mono f x (le_max_left _ _))
    by_cases hlt : k < sent f x m
    · exact ⟨m, hlt⟩
    · have he : sent f x m = k := by omega
      refine ⟨m + 1, ?_⟩
      rw [sent, he, ite_eq_left (hN (m + 1) (by dsimp [m]; omega))]

/-- The round stream produced by the greedy cylinder rule. -/
def simulatedPlay (f : Baire → Baire) (x : Baire) : Play := fun n => (x n, emission f x n)

lemma simulatedPlay_productive {f : Baire → Baire} (hf : Continuous f) (x : Baire) :
    Productive (simulatedPlay f x) := by
  intro N
  by_contra! h
  have hzero : ∀ n ≥ N, emission f x n = 0 := h
  have heq : ∀ n ≥ N, sent f x n = sent f x N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [sent_step, hzero n hn]; simpa using ih
  obtain ⟨n, hn⟩ := sent_unbounded hf x (sent f x N + 1)
  by_cases hN : N ≤ n
  · rw [heq n hN] at hn
    omega
  · have hle := sent_mono f x (show n ≤ N by omega)
    omega

/-- Count the genuine codes before a given round. -/
def outputCount (p : Play) : ℕ → ℕ
  | 0 => 0
  | n + 1 => outputCount p n + if (p n).2 = 0 then 0 else 1

lemma outputCount_passes {p : Play} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ i, a ≤ i → i < b → (p i).2 = 0) : outputCount p b = outputCount p a := by
  revert h
  induction b, hab using Nat.le_induction with
  | base => intro _; rfl
  | succ b hab ih =>
    intro h
    rw [outputCount, h b hab (Nat.lt_succ_self b), ite_eq_left rfl, Nat.add_zero]
    exact ih (fun i hai hib => h i hai (by omega))

lemma outputCount_next {p : Play} (hp : Productive p) (k : ℕ) :
    outputCount p (next p k) = outputCount p k := by
  apply outputCount_passes (next_spec hp k).1
  intro i hki hin
  by_contra hi
  have hle := next_le hp hki hi
  omega

lemma outputCount_genuineIndex {p : Play} (hp : Productive p) (k : ℕ) :
    outputCount p (genuineIndex p k) = k := by
  induction k with
  | zero => exact outputCount_next hp 0
  | succ k ih =>
    rw [genuineIndex, outputCount_next hp, outputCount, ite_eq_right (genuineIndex_nonzero hp k), ih]

lemma outputCount_simulatedPlay (f : Baire → Baire) (x : Baire) (n : ℕ) :
    outputCount (simulatedPlay f x) n = sent f x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [outputCount, ih, sent_step]
    rfl

lemma emission_value {f : Baire → Baire} {x : Baire} {n : ℕ} (h : emission f x n ≠ 0) :
    emission f x n - 1 = f x (sent f x n) := by
  have hk : Known f (seqPrefix x (n + 1)) (sent f x n) := by
    by_contra hk
    simp [emission, hk] at h
  rw [emission, ite_eq_left hk, Nat.add_sub_cancel]
  exact (hk x (mem_cyl_seqPrefix x _)).symm

def simulatedProductivePlay {f : Baire → Baire} (hf : Continuous f) (x : Baire) : ProductivePlay :=
  ⟨simulatedPlay f x, simulatedPlay_productive hf x⟩

lemma secondOutput_simulatedPlay {f : Baire → Baire} (hf : Continuous f) (x : Baire) :
    secondOutput (simulatedProductivePlay hf x) = f x := by
  funext k
  let p := simulatedPlay f x
  have hp : Productive p := simulatedPlay_productive hf x
  have hcnt := outputCount_genuineIndex hp k
  rw [outputCount_simulatedPlay] at hcnt
  change emission f x (genuineIndex p k) - 1 = f x k
  rw [emission_value (genuineIndex_nonzero hp k), hcnt]


/-- Extract I's finite input, including the current move, from an odd-length history. -/
def inputHistory (n : ℕ) (h : Fin (2 * n + 1) → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n + 1) => h ⟨2 * i.val, by omega⟩)

/-- Reconstruct previous emissions from the input history, then apply the cylinder rule. -/
def continuousStrategy (f : Baire → Baire) : SecondStrategy := fun n h =>
  emission f (extendFinseq (inputHistory n h)) n

lemma inputHistory_on_play (a : Baire) (n : ℕ) :
    inputHistory n (fun i => a i) = seqPrefix (firstOutput (roundPlay a)) (n + 1) := rfl

lemma continuousStrategy_on_play (f : Baire → Baire) (a : Baire) (n : ℕ) :
    continuousStrategy f n (fun i => a i) = emission f (firstOutput (roundPlay a)) n := by
  simp only [continuousStrategy, inputHistory_on_play]
  apply emission_congr
  intro i hi
  exact ((extendFinseq_mem_cyl (seqPrefix (firstOutput (roundPlay a)) (n + 1)))
    i (by simpa using hi)).trans (seqPrefix_get _ _)

lemma roundPlay_of_follows {f : Baire → Baire} {a : Baire}
    (ha : BaireFollowsII (continuousStrategy f) a) :
    roundPlay a = simulatedPlay f (firstOutput (roundPlay a)) := by
  funext n
  apply Prod.ext
  · rfl
  · exact (ha n).trans (continuousStrategy_on_play f a n)

/-- Every play following the strategy produces exactly the image under the continuous map. -/
theorem continuousStrategy_winning {f : Baire → Baire} (hf : Continuous f)
    {A B : Set Baire} (hred : A = f ⁻¹' B) : SecondWinning A B (continuousStrategy f) := by
  intro a ha
  let x := firstOutput (roundPlay a)
  have hm : simulatedPlay f x ∈ secondPayoff A B := by
    apply (mem_secondPayoff (simulatedProductivePlay hf x)).mpr
    rw [secondOutput_simulatedPlay]
    change x ∈ A ↔ f x ∈ B
    rw [hred]
    rfl
  change ¬ (roundPlay a ∉ secondPayoff A B)
  rw [roundPlay_of_follows ha]
  exact not_not.mpr hm

/-- The two constructions establish the full second-player strategy correspondence. -/
theorem secondWinning_iff_reducible {A B : Set Baire} :
    (∃ τ : SecondStrategy, SecondWinning A B τ) ↔ WadgeReducible A B := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact reducible_of_secondWinning hτ
  · rintro ⟨f, hf, hred⟩
    exact ⟨continuousStrategy f, continuousStrategy_winning hf hred⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: lemma
  title: Strategy correspondence
-/
theorem strategy_correspondence {A B : Set Baire} :
    ((∃ τ : SecondStrategy, SecondWinning A B τ) ↔ WadgeReducible A B) ∧
    (∀ σ : FirstStrategy, FirstWinning A B σ → WadgeReducible B Aᶜ) ∧
    (Determined A B → ¬ WadgeReducible A B → ∃ σ : FirstStrategy, FirstWinning A B σ) :=
  ⟨secondWinning_iff_reducible, fun _ h => reducible_compl_of_firstWinning h, firstWinning_of_not_reducible⟩

end PolishSpaceBook.WadgeGame
