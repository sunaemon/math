module

public import PolishSpaceBook.WadgeGamePayoff
public import PolishSpaceBook.TreeGames

@[expose] public section

/-!
# Continuous reductions extracted from Wadge strategies

Against II, prescribe I's input; against I, prescribe II's output without passes.
Finite-history induction proves that the resulting raw plays depend continuously
on the prescribed sequence. A winning second-player strategy guarantees productive
output, so continuous pass deletion supplies the reduction.
-/
noncomputable section
namespace PolishSpaceBook.WadgeGame
open Set Function Filter Topology TreeGames
open scoped Classical

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    For (1, $\Rightarrow$), fix a winning strategy $\sigma$ of II. Prescribe I's input $x$ and let II follow
    $\sigma$. The resulting play exists and is unique by the lemma on the play of two strategies in §{sec:determinacy}.
    If two inputs agree on their first $N$ coordinates, induction over the first $N$ rounds shows that the entire
    histories through those rounds agree: I supplies the same move, and II applies the same strategy to the same history.

    Because $\sigma$ wins, it produces infinitely many genuine moves against every $x$. Let $f_\sigma(x)$ be its
    output after deleting passes, and let $j_k(x)$ be the round at which its $k$-th genuine move is played.
    Agreement of the input through that round fixes this output coordinate:
    $$
    \restrict{x'}{j_k(x)+1}=\restrict{x}{j_k(x)+1}
    \quad\Longrightarrow\quad f_\sigma(x')(k)=f_\sigma(x)(k).
    $$
    Thus each coordinate is locally constant, and $f_\sigma$ is continuous. The winning condition gives
    $$x\in A\quad\Longleftrightarrow\quad f_\sigma(x)\in B,$$
    so $A=f_\sigma^{-1}(B)$.
-/
/-- Supply I's input independently of the preceding play. -/
def againstII (τ : SecondStrategy) (x : ℕ → ℕ) : ℕ → ℕ :=
  (baire_exists_joint_play (fun n _ => x n) τ).choose
lemma againstII_even (τ : SecondStrategy) (x : ℕ → ℕ) (n : ℕ) : againstII τ x (2 * n) = x n :=
  (baire_exists_joint_play (fun n _ => x n) τ).choose_spec.1 n
lemma againstII_follows (τ : SecondStrategy) (x : ℕ → ℕ) : BaireFollowsII τ (againstII τ x) :=
  (baire_exists_joint_play (fun n _ => x n) τ).choose_spec.2

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For (2), fix a winning strategy $\tau$ of I. Given $y\in\BaireSpace$, make II never pass and supply the codes
    $y(n)+1$. Keeping the full coded history, define
    $$
    \begin{aligned}
    p_0&:=\emptySeq,& a_n&:=\tau(p_n),\\
    p_{n+1}&:=p_n\concat(a_n,y(n)+1),& g(y)(n)&:=a_n.
    \end{aligned}
    $$
    If two inputs $y$ agree before coordinate $n$, induction gives the same $p_n$ and hence the same $a_n$.
    Therefore every coordinate of $g$ depends on a finite prefix, and $g$ is continuous. II's genuine output in
    this play is $y$. Since I follows $\tau$ and wins against this opponent who never passes,
    $$g(y)\in A\quad\Longleftrightarrow\quad y\notin B.$$
    Equivalently,
    $$y\in B\quad\Longleftrightarrow\quad g(y)\in\SetDifference{\BaireSpace}{A}.$$
    Hence $B=g^{-1}(\SetDifference{\BaireSpace}{A})$, as required.
-/
/-- Supply genuine II moves, encoded positively, so there are no passes. -/
def againstI (σ : FirstStrategy) (y : ℕ → ℕ) : ℕ → ℕ :=
  (baire_exists_joint_play σ (fun n _ => y n + 1)).choose
lemma againstI_odd (σ : FirstStrategy) (y : ℕ → ℕ) (n : ℕ) : againstI σ y (2 * n + 1) = y n + 1 :=
  (baire_exists_joint_play σ (fun n _ => y n + 1)).choose_spec.2 n
lemma againstI_follows (σ : FirstStrategy) (y : ℕ → ℕ) : BaireFollowsI σ (againstI σ y) :=
  (baire_exists_joint_play σ (fun n _ => y n + 1)).choose_spec.1

/-- Through round `N - 1`, II sees only I's first `N` input coordinates. -/
lemma againstII_prefix (τ : SecondStrategy) {x y : ℕ → ℕ} {N : ℕ}
    (h : ∀ n < N, x n = y n) : ∀ i < 2 * N, againstII τ x i = againstII τ y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases he : i % 2 = 0
    · obtain ⟨n, rfl⟩ : ∃ n, i = 2 * n := ⟨i / 2, by omega⟩
      rw [againstII_even, againstII_even]
      exact h n (by omega)
    · obtain ⟨n, rfl⟩ : ∃ n, i = 2 * n + 1 := ⟨i / 2, by omega⟩
      rw [againstII_follows τ x n, againstII_follows τ y n]
      congr 1
      funext j
      exact ih j.val j.isLt (by omega)

/-- I's move at round `N` depends only on II's preceding `N` moves. -/
lemma againstI_prefix (σ : FirstStrategy) {x y : ℕ → ℕ} {N : ℕ}
    (h : ∀ n < N, x n = y n) : ∀ i < 2 * N + 1, againstI σ x i = againstI σ y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases he : i % 2 = 0
    · obtain ⟨n, rfl⟩ : ∃ n, i = 2 * n := ⟨i / 2, by omega⟩
      rw [againstI_follows σ x n, againstI_follows σ y n]
      congr 1
      funext j
      exact ih j.val j.isLt (by omega)
    · obtain ⟨n, rfl⟩ : ∃ n, i = 2 * n + 1 := ⟨i / 2, by omega⟩
      rw [againstI_odd, againstI_odd, h n (by omega)]

lemma againstII_continuous (τ : SecondStrategy) : Continuous (againstII τ) := by
  apply continuous_pi
  intro i
  rw [continuous_iff_continuousAt]
  intro x
  apply Filter.EventuallyEq.continuousAt (y := againstII τ x i)
  filter_upwards [(isOpen_cyl (seqPrefix x (i + 1))).mem_nhds (mem_cyl_seqPrefix x _)] with y hy
  apply againstII_prefix τ (N := i + 1) _ i (by omega)
  intro j hj
  exact (hy j (by simpa using hj)).trans (seqPrefix_get x _)

lemma againstI_continuous (σ : FirstStrategy) : Continuous (againstI σ) := by
  apply continuous_pi
  intro i
  rw [continuous_iff_continuousAt]
  intro y
  apply Filter.EventuallyEq.continuousAt (y := againstI σ y i)
  filter_upwards [(isOpen_cyl (seqPrefix y (i + 1))).mem_nhds (mem_cyl_seqPrefix y _)] with z hz
  apply againstI_prefix σ (N := i + 1) _ i (by omega)
  intro j hj
  exact (hz j (by simpa using hj)).trans (seqPrefix_get y _)

variable {A B : Set (ℕ → ℕ)}

lemma againstII_mem_payoff {τ : SecondStrategy} (hτ : SecondWinning A B τ) (x : ℕ → ℕ) :
    roundPlay (againstII τ x) ∈ secondPayoff A B := by
  have h := hτ (againstII τ x) (againstII_follows τ x)
  simpa [integerPayoff] using h

lemma againstII_productive {τ : SecondStrategy} (hτ : SecondWinning A B τ) (x : ℕ → ℕ) :
    Productive (roundPlay (againstII τ x)) := by
  obtain ⟨p, _, hp⟩ := againstII_mem_payoff hτ x
  exact hp ▸ p.property

/-- A winning strategy guarantees that the induced play lies in the productive subspace. -/
def secondInducedPlay {τ : SecondStrategy} (hτ : SecondWinning A B τ) (x : ℕ → ℕ) : ProductivePlay :=
  ⟨roundPlay (againstII τ x), againstII_productive hτ x⟩

lemma secondInducedPlay_continuous {τ : SecondStrategy} (hτ : SecondWinning A B τ) :
    Continuous (secondInducedPlay hτ) :=
  (roundPlay_continuous.comp (againstII_continuous τ)).subtype_mk _

lemma firstOutput_secondInducedPlay {τ : SecondStrategy} (hτ : SecondWinning A B τ) (x : ℕ → ℕ) :
    firstOutput (secondInducedPlay hτ x).val = x := by
  funext n
  exact againstII_even τ x n

def secondReductionMap {τ : SecondStrategy} (hτ : SecondWinning A B τ) : (ℕ → ℕ) → (ℕ → ℕ) :=
  secondOutput ∘ secondInducedPlay hτ

/-- Delete passes from a winning response strategy to obtain its continuous reduction. -/
theorem reducible_of_secondWinning {τ : SecondStrategy} (hτ : SecondWinning A B τ) : WadgeReducible A B := by
  refine ⟨secondReductionMap hτ, secondOutput_continuous.comp (secondInducedPlay_continuous hτ), ?_⟩
  ext x
  have h := (mem_secondPayoff (secondInducedPlay hτ x)).mp (againstII_mem_payoff hτ x)
  simpa only [firstOutput_secondInducedPlay, secondReductionMap, comp_apply, mem_preimage] using h

lemma productive_of_noPass {p : Play} (hp : ∀ n, (p n).2 ≠ 0) : Productive p :=
  fun N => ⟨N, le_rfl, hp N⟩

lemma genuineIndex_of_noPass {p : Play} (hp : ∀ n, (p n).2 ≠ 0) (n : ℕ) : genuineIndex p n = n := by
  have hn (k : ℕ) : next p k = k :=
    le_antisymm (next_le (productive_of_noPass hp) le_rfl (hp k)) (next_spec (productive_of_noPass hp) k).1
  induction n with
  | zero => exact hn 0
  | succ n ih => simpa only [genuineIndex, ih] using hn (n + 1)

lemma againstI_noPass (σ : FirstStrategy) (y : ℕ → ℕ) (n : ℕ) :
    (roundPlay (againstI σ y) n).2 ≠ 0 := by
  change againstI σ y (2 * n + 1) ≠ 0
  rw [againstI_odd]
  omega

def firstInducedPlay (σ : FirstStrategy) (y : ℕ → ℕ) : ProductivePlay :=
  ⟨roundPlay (againstI σ y), productive_of_noPass (againstI_noPass σ y)⟩

lemma secondOutput_firstInducedPlay (σ : FirstStrategy) (y : ℕ → ℕ) :
    secondOutput (firstInducedPlay σ y) = y := by
  funext n
  change (roundPlay (againstI σ y) (genuineIndex (roundPlay (againstI σ y)) n)).2 - 1 = y n
  rw [genuineIndex_of_noPass (againstI_noPass σ y)]
  change againstI σ y (2 * n + 1) - 1 = y n
  rw [againstI_odd]
  omega

def firstReductionMap (σ : FirstStrategy) : (ℕ → ℕ) → (ℕ → ℕ) := firstOutput ∘ roundPlay ∘ againstI σ

/-- Test a first-player strategy only against non-passing opponents. -/
theorem reducible_compl_of_firstWinning {σ : FirstStrategy} (hσ : FirstWinning A B σ) :
    WadgeReducible B Aᶜ := by
  refine ⟨firstReductionMap σ,
    firstOutput_continuous.comp (roundPlay_continuous.comp (againstI_continuous σ)), ?_⟩
  ext y
  have hw := hσ (againstI σ y) (againstI_follows σ y)
  have hn : ¬ (firstOutput (firstInducedPlay σ y).val ∈ A ↔ secondOutput (firstInducedPlay σ y) ∈ B) :=
    fun h => hw ((mem_secondPayoff (firstInducedPlay σ y)).mpr h)
  rw [secondOutput_firstInducedPlay] at hn
  change (y ∈ B ↔ firstOutput (firstInducedPlay σ y).val ∉ A)
  tauto

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    This is immediate from the previous lemma: under determinacy one of I, II has a winning strategy, supplying one of the
    two reductions.
    \end{proof}
-/
/-- Determinacy chooses one of the two explicit continuous reductions. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: lemma
  title: Wadge
-/
theorem wadge_lemma (h : Determined A B) : WadgeReducible A B ∨ WadgeReducible B Aᶜ := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · exact Or.inr (reducible_compl_of_firstWinning hσ)
  · exact Or.inl (reducible_of_secondWinning hτ)

/-- The quoted Borel-determinacy theorem supplies the hypothesis of Wadge's lemma. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: corollary
  title: Semi-linear ordering principle
-/
theorem borel_semilinear
    (hA : MeasurableSet A) (hB : MeasurableSet B) : WadgeReducible A B ∨ WadgeReducible B Aᶜ :=
  wadge_lemma (determined_of_borel_determinacy hA hB)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Finally, under determinacy one player has a winning strategy. If $A\not\le_W B$, the implication already
    proved for II excludes a winning strategy for II. Thus I has one, and (2) gives the second reduction.
    \end{proof}
-/
lemma firstWinning_of_not_reducible (hdet : Determined A B) (hnot : ¬ WadgeReducible A B) :
    ∃ σ : FirstStrategy, FirstWinning A B σ := by
  rcases hdet with hI | ⟨τ, hτ⟩
  · exact hI
  · exact (hnot (reducible_of_secondWinning hτ)).elim

end PolishSpaceBook.WadgeGame
