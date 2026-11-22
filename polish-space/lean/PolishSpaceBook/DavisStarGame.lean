module

public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Davis's star game

Each round appends I's finite binary word and II's single bit. The latter
ensures growth even when I chooses the empty word. Strategies retain the full
history of the opponent; their own earlier moves can be reconstructed from it.
-/
noncomputable section
namespace PolishSpaceBook.DavisStarGame
open Set Function Filter Topology
open scoped Classical

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    In the \termdefineas{star game}{$*$-game} Player I plays finite binary strings $s_0, s_1, \ldots$ and Player II plays
    single bits $b_0, b_1,\ldots$; the play codes the real
    $$x \;:=\; s_0 \concat (b_0) \concat s_1 \concat (b_1) \concat \cdots \;\in\; \CantorSpace.$$
    Player I wins iff $x \in A$. The empty word is allowed, but every round adds at least the bit chosen by II,
    so the output is always an infinite binary sequence.

    A strategy of I can be written as $\sigma:\finseq{2}\to\finseq{2}$, with $\sigma(\restrict{b}{n})$ specifying
    I's word at round $n$. For II we write $\tau(h,t)$, where $h\in\finseq{(\finseq{2})}$ is the history of I's previous
    words and $t\in\finseq{2}$ is the current word. Each player retains the opponent's whole finite history;
    the player's own earlier moves are already determined by that history and the strategy.
-/
abbrev Cantor := ℕ → Bool
abbrev Words := ℕ → List Bool
abbrev FirstStrategy := List Bool → List Bool
abbrev SecondStrategy := List (List Bool) → List Bool → Bool

/-- The output after a finite number of complete rounds. -/
def outputPrefix (s : Words) (b : Cantor) : ℕ → List Bool
  | 0 => []
  | n + 1 => outputPrefix s b n ++ s n ++ [b n]

lemma partial_length (s : Words) (b : Cantor) (n : ℕ) : n ≤ (outputPrefix s b n).length := by
  induction n with
  | zero => simp [outputPrefix]
  | succ n ih => simp only [outputPrefix, List.length_append, List.length_singleton]; omega

lemma partial_prefix (s : Words) (b : Cantor) {n m : ℕ} (h : n ≤ m) :
    outputPrefix s b n <+: outputPrefix s b m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
    apply ih.trans
    simpa only [outputPrefix, List.append_assoc] using
      (List.prefix_append (outputPrefix s b m) (s m ++ [b m]))

/-- Each coordinate is available after at most that many rounds plus one. -/
def outcome (s : Words) (b : Cantor) (i : ℕ) : Bool :=
  (outputPrefix s b (i + 1))[i]'(by have := partial_length s b (i + 1); omega)

lemma outcome_get_partial (s : Words) (b : Cantor) {n i : ℕ}
    (hi : i < (outputPrefix s b n).length) : outcome s b i = (outputPrefix s b n)[i] := by
  unfold outcome
  rcases le_total (i + 1) n with h | h
  · exact (partial_prefix s b h).getElem (by have := partial_length s b (i + 1); omega)
  · exact ((partial_prefix s b h).getElem hi).symm

lemma outcome_extends (s : Words) (b : Cantor) (n : ℕ) :
    prefixOfSeq (outputPrefix s b n) (outcome s b) := by
  intro i hi
  exact outcome_get_partial s b hi

lemma outcome_unique (s : Words) (b : Cantor) {x : Cantor}
    (h : ∀ n, prefixOfSeq (outputPrefix s b n) x) : x = outcome s b := by
  funext i
  have hi : i < (outputPrefix s b (i + 1)).length := by
    have := partial_length s b (i + 1)
    omega
  exact (h (i + 1) i hi).trans (outcome_get_partial s b hi).symm

lemma outcome_bit (s : Words) (b : Cantor) (n : ℕ) :
    outcome s b ((outputPrefix s b n).length + (s n).length) = b n := by
  rw [outcome_get_partial s b (n := n + 1) (by simp [outputPrefix])]
  simp [outputPrefix]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Suppose first that I has a winning strategy $\sigma$. For each $b\in\CantorSpace$, let II play the bits of $b$.
    Define I's words and the output prefixes by
    $$
    \begin{aligned}
    p_0&:=\emptySeq,& s_n&:=\sigma(\restrict{b}{n}),\\
    p_{n+1}&:=p_n\concat s_n\concat(b(n)).
    \end{aligned}
    $$
    The prefixes extend one another and $|p_n|\ge n$. Thus there is a unique $f(b)\in\CantorSpace$ extending
    every $p_n$. This is the outcome of the play against $b$, so $f(b)\in A$.

    If $b$ and $c$ agree on their first $n$ bits, their words and output prefixes in the first $n$ rounds agree as well.
    Since $|p_n|\ge n$, this gives
    $$\restrict{b}{n}=\restrict{c}{n}\quad\Longrightarrow\quad
    \restrict{f(b)}{n}=\restrict{f(c)}{n}.$$
    Cylinder neighborhoods therefore show that $f$ is continuous. To prove injectivity, suppose $f(b)=f(c)$.
    Inductively assume that $b$ and $c$ agree before round $n$. The current prefix $p_n$ and word $s_n$ are then the same
    in both plays. At position $|p_n|+|s_n|$, the two outputs have bits $b(n)$ and $c(n)$, so these bits agree too.
    Induction gives $b=c$.

    Since $\CantorSpace$ is compact and the codomain is Hausdorff, this continuous injection is a closed embedding.
    Its image $f[\CantorSpace]\IncludedIn A$ is a Cantor set. This proves the first implication.
-/
/-- I's earlier words are determined by the history of II's bits. -/
def firstWords (σ : FirstStrategy) (b : Cantor) : Words := fun n => σ (seqPrefix b n)
def firstOutcome (σ : FirstStrategy) (b : Cantor) : Cantor := outcome (firstWords σ b) b

def FirstWinning (σ : FirstStrategy) (A : Set Cantor) : Prop :=
  ∀ b, firstOutcome σ b ∈ A

lemma seqPrefix_congr {b c : Cantor} {n : ℕ} (h : ∀ i < n, b i = c i) :
    seqPrefix b n = seqPrefix c n := by
  unfold seqPrefix
  congr 1
  funext i
  exact h i i.isLt

lemma first_partial_congr (σ : FirstStrategy) {b c : Cantor} {n : ℕ}
    (h : ∀ i < n, b i = c i) : outputPrefix (firstWords σ b) b n = outputPrefix (firstWords σ c) c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := seqPrefix_congr (n := n) (fun i hi => h i (by omega : i < n + 1))
    simp only [outputPrefix, firstWords, ih (fun i hi => h i (by omega)), hp, h n (by omega)]

lemma first_outcome_congr (σ : FirstStrategy) {b c : Cantor} {i : ℕ}
    (h : ∀ j < i + 1, b j = c j) : firstOutcome σ b i = firstOutcome σ c i := by
  unfold firstOutcome outcome
  simp only [first_partial_congr σ h]

lemma firstOutcome_prefix (σ : FirstStrategy) {b c : Cantor} {n : ℕ}
    (h : seqPrefix b n = seqPrefix c n) :
    seqPrefix (firstOutcome σ b) n = seqPrefix (firstOutcome σ c) n := by
  apply seqPrefix_congr
  intro i hi
  apply first_outcome_congr
  intro j hj
  have hh : prefixOfSeq (seqPrefix c n) b := h ▸ prefixOfSeq_seqPrefix b n
  exact (hh j (by simpa using (by omega : j < n))).trans (seqPrefix_get c _)

lemma firstOutcome_continuous (σ : FirstStrategy) : Continuous (firstOutcome σ) := by
  apply continuous_pi
  intro i
  rw [continuous_iff_continuousAt]
  intro b
  apply Filter.EventuallyEq.continuousAt (y := firstOutcome σ b i)
  filter_upwards [(isOpen_cyl (seqPrefix b (i + 1))).mem_nhds
    (mem_cyl_seqPrefix b (i + 1))] with c hc
  apply first_outcome_congr
  intro j hj
  exact (hc j (by simpa using hj)).trans (seqPrefix_get b _)

lemma firstOutcome_injective (σ : FirstStrategy) : Injective (firstOutcome σ) := by
  intro b c heq
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hp := first_partial_congr σ ih
    have hs : firstWords σ b n = firstWords σ c n := congrArg σ (seqPrefix_congr ih)
    have hb := outcome_bit (firstWords σ b) b n
    have hc := outcome_bit (firstWords σ c) c n
    change firstOutcome σ b _ = b n at hb
    change firstOutcome σ c _ = c n at hc
    rw [heq, hp, hs] at hb
    exact hb.symm.trans hc

/-- Compactness turns the explicit continuous injection into a closed embedding. -/
theorem firstOutcome_closedEmbedding (σ : FirstStrategy) :
    IsClosedEmbedding (firstOutcome σ) :=
  (firstOutcome_continuous σ).isClosedEmbedding (firstOutcome_injective σ)

theorem cantor_subset_of_firstWinning {σ : FirstStrategy} {A : Set Cantor}
    (h : FirstWinning σ A) :
    ∃ f : Cantor → Cantor, IsClosedEmbedding f ∧ range f ⊆ A :=
  ⟨firstOutcome σ, firstOutcome_closedEmbedding σ, by rintro _ ⟨b, rfl⟩; exact h b⟩


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Now suppose that II has a winning strategy $\tau$. For a finite history $h$ of I's words, let $p_h$ be the output
    already forced by $\tau$. Thus
    $$p_{\emptySeq}=\emptySeq,\qquad
    p_{h\concat(t)}=p_h\concat t\concat(\tau(h,t)).$$
    Let $E_h$ consist of the reals $x$ extending $p_h$ for which every $t\in\finseq{2}$ satisfies
    $$p_h\concat t\prefixOf x\quad\Longrightarrow\quad
    \tau(h,t)\ne x(|p_h|+|t|).$$
    These are precisely the targets for which the construction gets stuck at $h$.

    For fixed $h$, the set $E_h$ has at most one member. The prefix $p_h$ is fixed, and any remaining tail $y$ must satisfy
    $$y(k)=1-\tau(h,\restrict{y}{k})\qquad(k\in\omega).$$
    The first bit is therefore determined; after the first $k$ bits have been determined, this equation determines
    the next one. Induction proves uniqueness of the whole tail. Since finite histories form a countable set,
    $$E:=\bigcup_{h\in\finseq{(\finseq{2})}}E_h$$
    is countable.

    Fix $x\notin E$. Starting with $h_0:=\emptySeq$, recursively choose the shortest finite word $t$ such that
    $$p_{h_n}\concat t\prefixOf x,\qquad \tau(h_n,t)=x(|p_{h_n}|+|t|),$$
    and put $s_n:=t$ and $h_{n+1}:=h_n\concat(s_n)$. Initially $p_{h_0}\prefixOf x$.
    Whenever $p_{h_n}\prefixOf x$, the fact that $x\notin E_{h_n}$ guarantees such a word.
    For each length there is only one candidate matching the target tail, so the shortest word is well defined.
    Its matching response ensures $p_{h_{n+1}}\prefixOf x$. The recursion therefore continues for every round.
    Moreover, $|p_{h_n}|\ge n$, because every round adds one bit after I's word. The resulting infinite outcome is
    exactly $x$.

    II follows $\tau$ in this play, so $x\notin A$. We have proved that every $x\notin E$ is outside $A$.
    Thus $A\IncludedIn E$, and $A$ is countable.
    \end{proof}
-/
/-- II's earlier bits are determined by the complete history of I's words. -/
def secondBits (τ : SecondStrategy) (s : Words) : Cantor := fun n => τ (seqPrefix s n) (s n)
def secondOutcome (τ : SecondStrategy) (s : Words) : Cantor := outcome s (secondBits τ s)

def SecondWinning (τ : SecondStrategy) (A : Set Cantor) : Prop :=
  ∀ s, secondOutcome τ s ∉ A

/-- The output forced by II after a finite history of I's words. -/
def historyOutput (τ : SecondStrategy) (h : List (List Bool)) : List Bool :=
  match h with
  | [] => []
  | t :: h => t ++ [τ [] t] ++ historyOutput (fun q u => τ (t :: q) u) h

lemma historyOutput_append (τ : SecondStrategy) (h : List (List Bool)) (t : List Bool) :
    historyOutput τ (h ++ [t]) = historyOutput τ h ++ t ++ [τ h t] := by
  induction h generalizing τ with
  | nil => simp [historyOutput]
  | cons u h ih => simp [historyOutput, ih, List.append_assoc]

lemma historyOutput_length (τ : SecondStrategy) (h : List (List Bool)) :
    h.length ≤ (historyOutput τ h).length := by
  induction h generalizing τ with
  | nil => simp [historyOutput]
  | cons t h ih =>
    have := ih (fun q u => τ (t :: q) u)
    simp only [historyOutput, List.length_append, List.length_cons]
    omega

lemma historyOutput_seqPrefix (τ : SecondStrategy) (s : Words) (n : ℕ) :
    historyOutput τ (seqPrefix s n) = outputPrefix s (secondBits τ s) n := by
  induction n with
  | zero => simp [seqPrefix, historyOutput, outputPrefix]
  | succ n ih =>
    rw [seqPrefix_succ_eq_concat, historyOutput_append, ih]
    rfl

/-- A finite segment of the target following a given output prefix. -/
def targetWord (x : Cantor) (start k : ℕ) : List Bool := List.ofFn fun i : Fin k => x (start + i)

@[simp] lemma targetWord_length (x : Cantor) (start k : ℕ) : (targetWord x start k).length = k := by
  simp [targetWord]

lemma targetWord_prefix {p : List Bool} {x : Cantor} (hp : prefixOfSeq p x) (k : ℕ) :
    prefixOfSeq (p ++ targetWord x p.length k) x := by
  intro i hi
  simp only [List.get_eq_getElem, List.getElem_append]
  split_ifs with hip
  · exact hp i hip
  · simp only [targetWord, List.getElem_ofFn]
    congr 1
    omega

/-- A target gets stuck at this history when no finite matching extension lets II agree. -/
def Blocked (τ : SecondStrategy) (h : List (List Bool)) (x : Cantor) : Prop :=
  prefixOfSeq (historyOutput τ h) x ∧
    ∀ t, prefixOfSeq (historyOutput τ h ++ t) x →
      τ h t ≠ x ((historyOutput τ h).length + t.length)

lemma blocked_subsingleton (τ : SecondStrategy) (h : List (List Bool)) :
    {x | Blocked τ h x}.Subsingleton := by
  intro x hx y hy
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    let p := historyOutput τ h
    by_cases hip : i < p.length
    · exact (hx.1 i hip).trans (hy.1 i hip).symm
    · have hpi : p.length ≤ i := by omega
      let k := i - p.length
      have hk : p.length + k = i := by dsimp [k]; omega
      have hw : targetWord x p.length k = targetWord y p.length k := by
        unfold targetWord
        congr 1
        funext j
        exact ih (p.length + j) (by omega)
      have hbx := hx.2 _ (targetWord_prefix hx.1 k)
      have hby := hy.2 _ (targetWord_prefix hy.1 k)
      simp only [targetWord_length] at hbx hby
      change τ h (targetWord x p.length k) ≠ x (p.length + k) at hbx
      change τ h (targetWord y p.length k) ≠ y (p.length + k) at hby
      rw [hw, hk] at hbx
      rw [hk] at hby
      cases hxv : x i <;> cases hyv : y i <;>
        cases htv : τ h (targetWord y p.length k) <;> simp_all

lemma blocked_countable (τ : SecondStrategy) :
    (⋃ h : List (List Bool), {x | Blocked τ h x}).Countable :=
  Set.countable_iUnion (fun h => (blocked_subsingleton τ h).countable)


lemma eq_targetWord_of_prefix {p t : List Bool} {x : Cantor}
    (h : prefixOfSeq (p ++ t) x) : t = targetWord x p.length t.length := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hh := h (p.length + i) (by simp; omega)
    have hn : ¬ p.length + i < p.length := by omega
    simpa only [List.get_eq_getElem, List.getElem_append, dite_eq_right hn,
      Nat.add_sub_cancel_left, targetWord, List.getElem_ofFn] using hh.symm

lemma exists_matching_length {τ : SecondStrategy} {x : Cantor} {h : List (List Bool)}
    (hp : prefixOfSeq (historyOutput τ h) x) (hnb : ¬ Blocked τ h x) :
    ∃ k, τ h (targetWord x (historyOutput τ h).length k) = x ((historyOutput τ h).length + k) := by
  by_contra! hn
  apply hnb
  refine ⟨hp, fun t ht => ?_⟩
  simpa only [← eq_targetWord_of_prefix ht] using hn t.length

/-- Choose the shortest matching target segment whenever an extension exists. -/
def nextWord (τ : SecondStrategy) (x : Cantor) (h : List (List Bool)) : List Bool :=
  if he : ∃ k, τ h (targetWord x (historyOutput τ h).length k) =
      x ((historyOutput τ h).length + k) then
    targetWord x (historyOutput τ h).length (Nat.find he)
  else []

lemma nextWord_good {τ : SecondStrategy} {x : Cantor} {h : List (List Bool)}
    (hp : prefixOfSeq (historyOutput τ h) x) (hnb : ¬ Blocked τ h x) :
    prefixOfSeq (historyOutput τ (h ++ [nextWord τ x h])) x := by
  have he := exists_matching_length hp hnb
  unfold nextWord
  rw [dite_eq_left he, historyOutput_append]
  have hp' := targetWord_prefix hp (Nat.find he)
  have hb := Nat.find_spec he
  intro i hi
  by_cases hip : i < (historyOutput τ h ++ targetWord x (historyOutput τ h).length (Nat.find he)).length
  · simpa only [List.get_eq_getElem, List.getElem_append_left hip] using hp' i hip
  · have hieq : i = (historyOutput τ h).length + Nat.find he := by
      simp only [List.length_append, List.length_singleton, targetWord_length] at hi hip
      omega
    subst i
    have hlast (q : List Bool) (v : Bool) : (q ++ [v])[q.length]'(by simp) = v := by simp
    have hl := hlast (historyOutput τ h ++ targetWord x (historyOutput τ h).length (Nat.find he))
      (τ h (targetWord x (historyOutput τ h).length (Nat.find he)))
    simpa only [List.length_append, targetWord_length, List.get_eq_getElem] using hb.symm.trans hl.symm


/-- The attempted matching play, including its complete finite word history. -/
def chosenHistory (τ : SecondStrategy) (x : Cantor) : ℕ → List (List Bool)
  | 0 => []
  | n + 1 => chosenHistory τ x n ++ [nextWord τ x (chosenHistory τ x n)]

def chosenWords (τ : SecondStrategy) (x : Cantor) : Words :=
  fun n => nextWord τ x (chosenHistory τ x n)

lemma chosenWords_prefix (τ : SecondStrategy) (x : Cantor) (n : ℕ) :
    seqPrefix (chosenWords τ x) n = chosenHistory τ x n := by
  induction n with
  | zero => simp [seqPrefix, chosenHistory]
  | succ n ih => rw [seqPrefix_succ_eq_concat, ih]; rfl

lemma chosenHistory_good {τ : SecondStrategy} {x : Cantor}
    (hnb : ∀ h, ¬ Blocked τ h x) (n : ℕ) :
    prefixOfSeq (historyOutput τ (chosenHistory τ x n)) x := by
  induction n with
  | zero => simp [chosenHistory, historyOutput, prefixOfSeq]
  | succ n ih => exact nextWord_good ih (hnb _)

/-- Outside the countable set of blocked targets, the recursion produces the target exactly. -/
theorem secondOutcome_chosenWords {τ : SecondStrategy} {x : Cantor}
    (hnb : ∀ h, ¬ Blocked τ h x) : secondOutcome τ (chosenWords τ x) = x := by
  funext i
  have hp := chosenHistory_good hnb (i + 1)
  rw [← chosenWords_prefix, historyOutput_seqPrefix] at hp
  have hi : i < (outputPrefix (chosenWords τ x) (secondBits τ (chosenWords τ x)) (i + 1)).length := by
    have := partial_length (chosenWords τ x) (secondBits τ (chosenWords τ x)) (i + 1)
    omega
  exact (hp i hi).symm

/-- A winning payoff is contained in the countable union of the blocked singletons. -/
theorem countable_of_secondWinning {τ : SecondStrategy} {A : Set Cantor}
    (hτ : SecondWinning τ A) : A.Countable := by
  apply (blocked_countable τ).mono
  intro x hx
  by_contra hn
  have hnb : ∀ h, ¬ Blocked τ h x := by simpa only [mem_iUnion, mem_ofPred_eq, not_exists] using hn
  have hw := hτ (chosenWords τ x)
  rw [secondOutcome_chosenWords hnb] at hw
  exact hw hx


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The following game theorem is due to Davis [@Davis1964].
-/
/-- The two alternatives of Davis's theorem, with the constructed closed embedding. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Davis
-/
theorem davis_theorem (A : Set Cantor) :
    (∀ σ, FirstWinning σ A → ∃ f : Cantor → Cantor, IsClosedEmbedding f ∧ range f ⊆ A) ∧
    (∀ τ, SecondWinning τ A → A.Countable) :=
  ⟨fun _ h => cantor_subset_of_firstWinning h, fun _ h => countable_of_secondWinning h⟩

/-- Determinacy gives the perfect-set alternative for the original payoff. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: corollary
  excerpt: |
    If the $*$-game on $A\IncludedIn\CantorSpace$ is determined, then $A$ is countable or contains a Cantor set. \end{corollary*}
-/
theorem perfect_set_alternative {A : Set Cantor}
    (h : (∃ σ, FirstWinning σ A) ∨ ∃ τ, SecondWinning τ A) :
    A.Countable ∨ ∃ f : Cantor → Cantor, IsClosedEmbedding f ∧ range f ⊆ A := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · exact Or.inr (cantor_subset_of_firstWinning hσ)
  · exact Or.inl (countable_of_secondWinning hτ)

end PolishSpaceBook.DavisStarGame
