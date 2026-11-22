module

public import PolishSpaceBook.TreeGames
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-!
# A game defeating every strategy

Well-order both strategy spaces with the initial ordinal of the continuum.
At each stage choose two compatible plays avoiding all earlier choices and
one another. Their disjoint ranges give the non-determined payoff.
-/
noncomputable section
namespace PolishSpaceBook.UndeterminedGame
open Set Function Cardinal TreeGames
open scoped Classical Cardinal

abbrev Baire := ℕ → ℕ

lemma card_baire : #Baire = 𝔠 := by
  simp [Baire, aleph0_power_aleph0]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    For each player, the set of finite histories at which that player moves is countably infinite.
    A strategy is an arbitrary function from that set to $\omega$, so each strategy space has cardinality
    $\alephNull^{\alephNull}=2^{\alephNull}=\bethCard{1}$.
-/
/-- Finite histories at the rounds of either player form a countably infinite type. -/
lemma card_histories (offset : ℕ) : #(Σ n : ℕ, Fin (2 * n + offset) → ℕ) = ℵ₀ := by
  let f : ℕ → (Σ n : ℕ, Fin (2 * n + offset) → ℕ) := fun n => ⟨n, fun _ => 0⟩
  have hf : Injective f := fun _ _ h => congrArg Sigma.fst h
  let : Infinite (Σ n : ℕ, Fin (2 * n + offset) → ℕ) := Infinite.of_injective f hf
  exact mk_eq_aleph0 _

lemma card_first_strategies : #BaireIStrategy = 𝔠 := by
  change #((n : ℕ) → (Fin (2 * n) → ℕ) → ℕ) = _
  rw [← mk_congr (Equiv.piCurry (fun n (_ : Fin (2 * n) → ℕ) => ℕ))]
  rw [mk_arrow, mk_nat, show #(Σ n : ℕ, Fin (2 * n) → ℕ) = ℵ₀ by simp]
  simp [aleph0_power_aleph0]

lemma card_second_strategies : #BaireIIStrategy = 𝔠 := by
  change #((n : ℕ) → (Fin (2 * n + 1) → ℕ) → ℕ) = _
  rw [← mk_congr (Equiv.piCurry (fun n (_ : Fin (2 * n + 1) → ℕ) => ℕ))]
  rw [mk_arrow, mk_nat, card_histories 1]
  simp [aleph0_power_aleph0]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A fixed strategy also has exactly $\bethCard{1}$ compatible plays. For an I-strategy $\sigma$, let the opponent
    play any prescribed sequence $b\in\BaireSpace$, using $b(n)$ as the move at round $n$.
    The play of these two strategies exists and is unique by the earlier lemma, and its odd coordinates are
    exactly $b$. Distinct choices of $b$ therefore give distinct compatible plays. The upper bound holds because
    all plays lie in $\BaireSpace$. For a II-strategy, prescribe the even coordinates in the same way.
-/
/-- The opponent can prescribe an arbitrary sequence of odd coordinates. -/
def firstCompatible (σ : BaireIStrategy) (b : Baire) : Baire :=
  (baire_exists_joint_play σ (fun n _ => b n)).choose
lemma firstCompatible_follows (σ : BaireIStrategy) (b : Baire) :
    BaireFollowsI σ (firstCompatible σ b) :=
  (baire_exists_joint_play σ (fun n _ => b n)).choose_spec.1
lemma firstCompatible_odd (σ : BaireIStrategy) (b : Baire) (n : ℕ) :
    firstCompatible σ b (2 * n + 1) = b n :=
  (baire_exists_joint_play σ (fun n _ => b n)).choose_spec.2 n

/-- The opponent can prescribe an arbitrary sequence of even coordinates. -/
def secondCompatible (τ : BaireIIStrategy) (b : Baire) : Baire :=
  (baire_exists_joint_play (fun n _ => b n) τ).choose
lemma secondCompatible_follows (τ : BaireIIStrategy) (b : Baire) :
    BaireFollowsII τ (secondCompatible τ b) :=
  (baire_exists_joint_play (fun n _ => b n) τ).choose_spec.2
lemma secondCompatible_even (τ : BaireIIStrategy) (b : Baire) (n : ℕ) :
    secondCompatible τ b (2 * n) = b n :=
  (baire_exists_joint_play (fun n _ => b n) τ).choose_spec.1 n

lemma card_first_compatible (σ : BaireIStrategy) : #{x : Baire | BaireFollowsI σ x} = 𝔠 := by
  apply le_antisymm
  · exact (mk_subtype_le _).trans card_baire.le
  · rw [← card_baire]
    apply mk_le_of_injective (f := fun b : Baire =>
      (⟨firstCompatible σ b, firstCompatible_follows σ b⟩ : {x : Baire | BaireFollowsI σ x}))
    intro b c h
    funext n
    have hh := congrArg (fun x : {x : Baire | BaireFollowsI σ x} => x.val (2 * n + 1)) h
    simpa only [firstCompatible_odd] using hh

lemma card_second_compatible (τ : BaireIIStrategy) : #{x : Baire | BaireFollowsII τ x} = 𝔠 := by
  apply le_antisymm
  · exact (mk_subtype_le _).trans card_baire.le
  · rw [← card_baire]
    apply mk_le_of_injective (f := fun b : Baire =>
      (⟨secondCompatible τ b, secondCompatible_follows τ b⟩ : {x : Baire | BaireFollowsII τ x}))
    intro b c h
    funext n
    have hh := congrArg (fun x : {x : Baire | BaireFollowsII τ x} => x.val (2 * n)) h
    simpa only [secondCompatible_even] using hh

lemma exists_fresh {Q S : Set Baire} (hQ : #Q = 𝔠) (hS : #S < 𝔠) : ∃ x ∈ Q, x ∉ S := by
  by_contra! h
  have hle := mk_le_mk_of_subset h
  rw [hQ] at hle
  exact (not_le_of_gt hS) hle

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Let $\kappa$ be the initial ordinal of cardinality $\bethCard{1}$. Choice gives enumerations
    $$\Sequence{\sigma_\alpha}{\alpha<\kappa},\qquad\Sequence{\tau_\alpha}{\alpha<\kappa}$$
    of the I-strategies and II-strategies. At each stage we choose a pair of plays $\Pair{x_\alpha}{y_\alpha}$.
    The first will defeat $\sigma_\alpha$ by being outside the final payoff; the second will defeat $\tau_\alpha$
    by being inside it.
-/
/-- The initial ordinal is essential: each proper initial segment is small. -/
abbrev Stage := (𝔠 : Cardinal.{0}).ord.ToType
lemma card_stage : #Stage = 𝔠 := by simp [Stage]
lemma card_predecessors (a : Stage) : #(Iio a) < 𝔠 := by
  simpa [Stage] using Cardinal.mk_Iio_lt a (by simp [Stage])

def enumFirst : Stage ≃ BaireIStrategy :=
  (Cardinal.eq.mp (card_stage.trans card_first_strategies.symm)).some
def enumSecond : Stage ≃ BaireIIStrategy :=
  (Cardinal.eq.mp (card_stage.trans card_second_strategies.symm)).some

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Use the transfinite-recursion principle of Appendix §{sec:ordinals-induction}. Given the pairs chosen before
    stage $\alpha$, put
    $$P_\alpha:=\{y_\beta:\beta<\alpha\},\qquad N_\alpha:=\{x_\beta:\beta<\alpha\}.$$
    Choose $x_\alpha$ following $\sigma_\alpha$ and then $y_\alpha$ following $\tau_\alpha$, subject to
    $$
    \begin{aligned}
    x_\alpha&\notin P_\alpha\cup N_\alpha,\\
    y_\alpha&\notin P_\alpha\cup N_\alpha\cup\{x_\alpha\}.
    \end{aligned}
    $$
    At stage zero both earlier sets are empty. These definitions collect the earlier choices at successor
    and limit stages alike.
-/
/-- Both earlier coordinates are forbidden, regardless of how the history was chosen. -/
def earlier (a : Stage) (h : ∀ b, b < a → Baire × Baire) : Set Baire :=
  range (fun b : Iio a => (h b.val b.property).1) ∪
    range (fun b : Iio a => (h b.val b.property).2)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    To justify every choice, both earlier sets are images of the ordinal $\alpha$, so
    $$|P_\alpha|,|N_\alpha|\le|\alpha|.$$
    Because $\kappa$ is the initial ordinal of cardinality continuum, $|\alpha|<2^{\alephNull}$.
    Cardinal arithmetic for the infinite cardinal $2^{\alephNull}$ gives
    $$
    \begin{aligned}
    |P_\alpha\cup N_\alpha|
    &\le |P_\alpha\cup N_\alpha\cup\{x_\alpha\}|\\
    &\le 2|\alpha|+1<2^{\alephNull}.
    \end{aligned}
    $$
    A compatible-play set has cardinality $2^{\alephNull}$, so it cannot be contained in either forbidden set.
    This proves existence of both choices from any earlier history. Fixing a choice from each nonempty set of
    admissible pairs makes the recursion clause a function, as required by transfinite recursion.
    Only a finite union of small sets is used at each stage; no regularity assumption on the continuum is needed.
-/
lemma earlier_small (a : Stage) (h : ∀ b, b < a → Baire × Baire) : #(earlier a h) < 𝔠 := by
  apply (mk_union_le _ _).trans_lt
  exact Cardinal.add_lt_of_lt aleph0_le_continuum
    (mk_range_le.trans_lt (card_predecessors a)) (mk_range_le.trans_lt (card_predecessors a))

lemma exists_fresh_pair (a : Stage) (h : ∀ b, b < a → Baire × Baire) :
    ∃ z : Baire × Baire, BaireFollowsI (enumFirst a) z.1 ∧
      BaireFollowsII (enumSecond a) z.2 ∧ z.1 ∉ earlier a h ∧ z.2 ∉ earlier a h ∧ z.1 ≠ z.2 := by
  obtain ⟨x, hx, hxf⟩ := exists_fresh (card_first_compatible (enumFirst a)) (earlier_small a h)
  have hs : #(insert x (earlier a h) : Set Baire) < 𝔠 :=
    mk_insert_le.trans_lt (Cardinal.add_one_lt_of_lt aleph0_le_continuum (earlier_small a h))
  obtain ⟨y, hy, hyf⟩ := exists_fresh (card_second_compatible (enumSecond a)) hs
  exact ⟨(x, y), hx, hy, hxf, fun hyh => hyf (Or.inr hyh), fun hxy => hyf (Or.inl hxy.symm)⟩

def choosePair (a : Stage) (h : ∀ b, b < a → Baire × Baire) : Baire × Baire :=
  (exists_fresh_pair a h).choose

def pair : Stage → Baire × Baire := WellFounded.fix wellFounded_lt choosePair

lemma pair_eq (a : Stage) : pair a = choosePair a (fun b _ => pair b) :=
  WellFounded.fix_eq _ _ _

lemma pair_spec (a : Stage) : BaireFollowsI (enumFirst a) (pair a).1 ∧
    BaireFollowsII (enumSecond a) (pair a).2 ∧
    (pair a).1 ∉ earlier a (fun b _ => pair b) ∧
    (pair a).2 ∉ earlier a (fun b _ => pair b) ∧ (pair a).1 ≠ (pair a).2 := by
  have h := (exists_fresh_pair a (fun b _ => pair b)).choose_spec
  have hp := (pair_eq a).symm
  dsimp only [choosePair] at hp
  rw [hp] at h
  exact h


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    No $x_\alpha$ equals any $y_\beta$. If $\alpha<\beta$, then $x_\alpha\in N_\beta$ and the choice of $y_\beta$
    excludes equality. If $\beta<\alpha$, then $y_\beta\in P_\alpha$ and the choice of $x_\alpha$ excludes equality.
    At the same stage, $y_\alpha\ne x_\alpha$ by construction. Thus the two ranges of chosen plays are disjoint.
-/
/-- A first-player counterplay never equals a second-player counterplay. -/
lemma first_ne_second (a b : Stage) : (pair a).1 ≠ (pair b).2 := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · intro he
    exact (pair_spec b).2.2.2.1 (Or.inl ⟨⟨a, hab⟩, he⟩)
  · exact (pair_spec a).2.2.2.2
  · intro he
    exact (pair_spec a).2.2.1 (Or.inr ⟨⟨b, hba⟩, he.symm⟩)

def positiveBefore (a : Stage) : Set Baire := range (fun b : Iio a => (pair b.val).2)
def negativeBefore (a : Stage) : Set Baire := range (fun b : Iio a => (pair b.val).1)

lemma positiveBefore_bound (a : Stage) : #(positiveBefore a) ≤ #(Iio a) := mk_range_le
lemma negativeBefore_bound (a : Stage) : #(negativeBefore a) ≤ #(Iio a) := mk_range_le
lemma before_disjoint (a : Stage) : Disjoint (positiveBefore a) (negativeBefore a) := by
  rw [Set.disjoint_left]
  rintro x ⟨b, rfl⟩ ⟨c, hc⟩
  exact first_ne_second c.val b.val hc

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Define the final payoff by
    $$A:=\{y_\alpha:\alpha<\kappa\}.$$
    For every I-strategy $\sigma_\alpha$, the play $x_\alpha$ follows it and lies outside $A$.
    For every II-strategy $\tau_\alpha$, the play $y_\alpha$ follows it and belongs to $A$.
    Neither player can therefore have a winning strategy for this payoff.
    \end{proof}
-/
/-- Include exactly the selected counterplays to Player II. -/
def payoff : Set Baire := range (fun a => (pair a).2)

lemma defeat_first (σ : BaireIStrategy) : ∃ x, BaireFollowsI σ x ∧ x ∉ payoff := by
  let a := enumFirst.symm σ
  refine ⟨(pair a).1, ?_, ?_⟩
  · simpa only [a, Equiv.apply_symm_apply] using (pair_spec a).1
  · rintro ⟨b, hb⟩
    exact first_ne_second a b hb.symm

lemma defeat_second (τ : BaireIIStrategy) : ∃ y, BaireFollowsII τ y ∧ y ∈ payoff := by
  let a := enumSecond.symm τ
  refine ⟨(pair a).2, ?_, mem_range_self a⟩
  simpa only [a, Equiv.apply_symm_apply] using (pair_spec a).2.1

/-- Diagonalization defeats both sides, without a determinacy hypothesis. -/
theorem payoff_not_determined : ¬ BaireDetermined payoff := by
  rintro (⟨σ, hσ⟩ | ⟨τ, hτ⟩)
  · obtain ⟨x, hx, hnot⟩ := defeat_first σ
    exact hnot (hσ x hx)
  · obtain ⟨y, hy, hmem⟩ := defeat_second τ
    exact hτ y hy hmem

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: An undetermined game under Choice
-/
theorem exists_undetermined : ∃ A : Set Baire, ¬ BaireDetermined A :=
  ⟨payoff, payoff_not_determined⟩

end PolishSpaceBook.UndeterminedGame
