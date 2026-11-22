module

public import PolishSpaceBook.DavisStarGame
public import PolishSpaceBook.TreeGames

@[expose] public section

/-!
# Natural-number coding of Davis's star game

Only canonical codes of finite binary words are legal at I's turns; II uses
0 and 1. This avoids ambiguities when transferring a coded strategy back to
word and bit histories. The output map is continuous on the closed branch space.
-/
noncomputable section
namespace PolishSpaceBook.DavisStarGame
open Set Function Filter Topology TreeGames.GameTree
open scoped Classical

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    To apply integer-game determinacy, fix an injective code $\iota:\finseq{2}\to\omega$ and let
    $C:=\iota[\finseq{2}]$. Only codes in $C$ may be used at I's turns; II uses the integers $0$ and $1$.
    Let $T\IncludedIn\finseq{\omega}$ consist of the finite sequences whose entries at even positions belong to $C$
    and whose entries at odd positions belong to $2$. A branch $a\in\TreeBody{T}$ decodes to
    $$s_n:=\iota^{-1}(a(2n)),\qquad b(n):=a(2n+1).$$
    Let $\pi(a)$ be the resulting infinite concatenation of these words and bits.
-/
abbrev wordCode (s : List Bool) : ℕ := Encodable.encode s
def decodeWord (n : ℕ) : List Bool := (Encodable.decode (α := List Bool) n).getD []
abbrev bitCode (b : Bool) : ℕ := b.toNat
def decodeBit (n : ℕ) : Bool := n == 1

@[simp] lemma decodeWord_code (s : List Bool) : decodeWord (wordCode s) = s := by
  simp [decodeWord, wordCode]
@[simp] lemma decodeBit_code (b : Bool) : decodeBit (bitCode b) = b := by cases b <;> rfl
lemma code_decodeWord {n : ℕ} (h : n ∈ range wordCode) : wordCode (decodeWord n) = n := by
  obtain ⟨s, rfl⟩ := h
  simp
lemma code_decodeBit {n : ℕ} (h : n ≤ 1) : bitCode (decodeBit n) = n := by
  interval_cases n <;> rfl

/-- Legal coordinates alternate canonical word codes and bit codes. -/
def MoveLegal (i a : ℕ) : Prop := if i % 2 = 0 then a ∈ range wordCode else a ≤ 1
def CodeLegal (s : List ℕ) : Prop := ∀ i (hi : i < s.length), MoveLegal i s[i]

lemma codeLegal_prefix {s t : List ℕ} (ht : CodeLegal t) (hst : s <+: t) : CodeLegal s := by
  intro i hi
  rw [hst.getElem hi]
  exact ht i (hi.trans_le hst.length_le)

lemma codeLegal_append {s : List ℕ} (hs : CodeLegal s) {a : ℕ}
    (ha : MoveLegal s.length a) : CodeLegal (s ++ [a]) := by
  intro i hi
  by_cases his : i < s.length
  · simpa only [List.getElem_append_left his] using hs i his
  · have hie : i = s.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using ha

lemma codeLegal_nil : CodeLegal [] := by intro i hi; simp at hi

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The coordinate conditions are preserved by taking prefixes. Every node has a legal successor: use
    $\iota(\emptySeq)$ at an I-turn and $0$ at an II-turn. Thus $T$ is pruned, and its body is closed in $\BaireSpace$,
    hence Polish. If two branches agree on their first $2n$ codes, their first $n$ words and bits agree.
    The output after these rounds has length at least $n$, so
    $$\restrict{a}{2n}=\restrict{a'}{2n}\quad\Longrightarrow\quad
    \restrict{\pi(a)}{n}=\restrict{\pi(a')}{n}.$$
    This proves continuity using cylinder neighborhoods. The payoff identity is the definition of I's win.
    \end{proof}
-/
/-- Every legal node has a successor, including positions of odd length. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Integer coding of the $*$-game
-/
def codeTree : TreeGames.GameTree ℕ where
  nodes := {s | CodeLegal s}
  subtree := fun _ _ ht hst => codeLegal_prefix ht hst
  root_mem := codeLegal_nil
  successor := by
    intro s hs
    by_cases he : s.length % 2 = 0
    · exact ⟨wordCode [], codeLegal_append hs (by rw [MoveLegal, ite_eq_left he]; exact mem_range_self [])⟩
    · exact ⟨0, codeLegal_append hs (by simp [MoveLegal, he])⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Integer coding of the $*$-game
-/
theorem codeTree_pruned : IsPruned codeTree.nodes := codeTree.isPruned

instance cantor_polish : PolishSpace Cantor := by
  let : ∀ _ : ℕ, PolishSpace Bool := fun _ => inferInstance
  exact countable_product_polish

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Integer coding of the $*$-game
-/
instance codePlay_polish : PolishSpace codeTree.Play :=
  (isClosed_treeBody codeTree.nodes).polishSpace

lemma play_move_legal (p : codeTree.Play) (i : ℕ) : MoveLegal i (p.val i) := by
  have h := p.property (i + 1) i (by simp)
  simpa only [seqPrefix, List.getElem_ofFn] using h

def decodedWords (p : codeTree.Play) : Words := fun n => decodeWord (p.val (2 * n))
def decodedBits (p : codeTree.Play) : Cantor := fun n => decodeBit (p.val (2 * n + 1))
def codeOutcome (p : codeTree.Play) : Cantor := outcome (decodedWords p) (decodedBits p)
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Integer coding of the $*$-game
-/
def codePayoff (A : Set Cantor) : Set codeTree.Play := codeOutcome ⁻¹' A

/-- Interleave the canonical codes of a word-and-bit play. -/
def playWord (s : Words) (b : Cantor) (i : ℕ) : ℕ :=
  if i % 2 = 0 then wordCode (s (i / 2)) else bitCode (b (i / 2))

@[simp] lemma playWord_even (s : Words) (b : Cantor) (n : ℕ) :
    playWord s b (2 * n) = wordCode (s n) := by simp [playWord]
@[simp] lemma playWord_odd (s : Words) (b : Cantor) (n : ℕ) :
    playWord s b (2 * n + 1) = bitCode (b n) := by simp [playWord, Nat.add_div]

lemma playWord_legal (s : Words) (b : Cantor) (n : ℕ) : CodeLegal (seqPrefix (playWord s b) n) := by
  intro i hi
  simp only [seqPrefix, List.getElem_ofFn, MoveLegal, playWord]
  split_ifs
  · exact mem_range_self _
  · cases b (i / 2) <;> decide

def codePlay (s : Words) (b : Cantor) : codeTree.Play := ⟨playWord s b, playWord_legal s b⟩

@[simp] lemma decodedWords_codePlay (s : Words) (b : Cantor) : decodedWords (codePlay s b) = s := by
  funext n
  simp [decodedWords, codePlay]
@[simp] lemma decodedBits_codePlay (s : Words) (b : Cantor) : decodedBits (codePlay s b) = b := by
  funext n
  simp [decodedBits, codePlay]
@[simp] lemma codeOutcome_codePlay (s : Words) (b : Cantor) : codeOutcome (codePlay s b) = outcome s b := by
  simp [codeOutcome]

lemma playWord_prefix_succ (s : Words) (b : Cantor) (n : ℕ) :
    seqPrefix (playWord s b) (2 * (n + 1)) =
      seqPrefix (playWord s b) (2 * n) ++ [wordCode (s n), bitCode (b n)] := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    seqPrefix_succ_eq_concat, seqPrefix_succ_eq_concat]
  simp [List.append_assoc]

lemma outputPrefix_congr {s t : Words} {b c : Cantor} {n : ℕ}
    (hs : ∀ i < n, s i = t i) (hb : ∀ i < n, b i = c i) :
    outputPrefix s b n = outputPrefix t c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [outputPrefix, ih (fun i hi => hs i (by omega)) (fun i hi => hb i (by omega)),
      hs n (by omega), hb n (by omega)]

lemma codeOutcome_coordinate_eq {p q : codeTree.Play} {i : ℕ}
    (h : ∀ j < 2 * (i + 1), p.val j = q.val j) : codeOutcome p i = codeOutcome q i := by
  have hp := outputPrefix_congr (s := decodedWords p) (t := decodedWords q)
    (b := decodedBits p) (c := decodedBits q) (n := i + 1)
    (fun j hj => congrArg decodeWord (h (2 * j) (by omega)))
    (fun j hj => congrArg decodeBit (h (2 * j + 1) (by omega)))
  unfold codeOutcome outcome
  simp only [hp]

lemma codeOutcome_prefix {p q : codeTree.Play} {n : ℕ}
    (h : seqPrefix p.val (2 * n) = seqPrefix q.val (2 * n)) :
    seqPrefix (codeOutcome p) n = seqPrefix (codeOutcome q) n := by
  apply seqPrefix_congr
  intro i hi
  apply codeOutcome_coordinate_eq
  intro j hj
  have hh : prefixOfSeq (seqPrefix q.val (2 * n)) p.val := h ▸ prefixOfSeq_seqPrefix p.val (2 * n)
  exact (hh j (by simpa using (by omega : j < 2 * n))).trans (seqPrefix_get q.val _)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Integer coding of the $*$-game
-/
lemma codeOutcome_continuous : Continuous codeOutcome := by
  apply continuous_pi
  intro i
  rw [continuous_iff_continuousAt]
  intro p
  apply Filter.EventuallyEq.continuousAt (y := codeOutcome p i)
  filter_upwards [((isOpen_cyl (seqPrefix p.val (2 * (i + 1)))).preimage
    continuous_subtype_val).mem_nhds (mem_cyl_seqPrefix p.val (2 * (i + 1)))] with q hq
  have hcoords : ∀ j < 2 * (i + 1), q.val j = p.val j := by
    intro j hj
    exact (hq j (by simpa using hj)).trans (seqPrefix_get p.val _)
  exact codeOutcome_coordinate_eq hcoords


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    First let $\widehat\sigma$ be a coded winning strategy for I. Keep the entire simulated code history $q_n$,
    starting with $q_0:=\emptySeq$. After II's previous bits have been supplied, set
    $$
    \begin{aligned}
    a_n&:=\widehat\sigma(q_n),& s_n&:=c^{-1}(a_n),\\
    q_{n+1}&:=q_n\concat(a_n,b(n)).
    \end{aligned}
    $$
    The history $q_n$ has length $2n$ and is legal. Therefore $a_n\in C$, and $s_n$ is well defined.
    Appending the bit $b(n)$ preserves legality. The chosen word depends only on the preceding bit history,
    so it defines a strategy for I. When that strategy is followed, the canonical code of $s_n$ is exactly $a_n$.
    Thus the coded play follows $\widehat\sigma$ and has the same concatenated outcome as the original play.
    Its outcome belongs to $A$.

    Now let $\widehat\tau$ be a coded winning strategy for II. Again start with $q_0:=\emptySeq$ and retain the full
    code history. When I supplies $s_n$, set
    $$
    \begin{aligned}
    a_n&:=c(s_n),& b(n)&:=\widehat\tau(q_n\concat(a_n)),\\
    q_{n+1}&:=q_n\concat(a_n,b(n)).
    \end{aligned}
    $$
    Appending $a_n$ is legal, and the strategy supplies a legal bit $b(n)\in2$. Hence the histories remain legal.
    This response depends only on I's previous words and current word, so it defines a strategy for II.
    The coded play follows $\widehat\tau$, and decoding preserves its concatenated outcome. That outcome is outside
    $A$, as required.
    \end{proof}
-/
/-- Off-turn or illegal histories receive a fallback; all simulated histories are legal. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting coded $*$-game strategies
-/
def answerCode {player : Bool} (σ : codeTree.Strategy player) (h : List ℕ) : ℕ :=
  if hh : CodeLegal h ∧ turn h = player then (σ ⟨h, hh.1⟩ hh.2).val else 0

lemma answerCode_eq {player : Bool} (σ : codeTree.Strategy player) {h : List ℕ}
    (hh : CodeLegal h) (ht : turn h = player) : answerCode σ h = (σ ⟨h, hh⟩ ht).val := by
  simp only [answerCode, dite_eq_left (show CodeLegal h ∧ turn h = player from ⟨hh, ht⟩)]

lemma answerCode_position {player : Bool} (σ : codeTree.Strategy player)
    (q : codeTree.Position) (ht : turn q.val = player) : answerCode σ q.val = (σ q ht).val := by
  exact answerCode_eq σ q.property ht

lemma answerCode_legal {player : Bool} (σ : codeTree.Strategy player) {h : List ℕ}
    (hh : CodeLegal h) (ht : turn h = player) : CodeLegal (h ++ [answerCode σ h]) := by
  rw [answerCode_eq σ hh ht]
  exact (σ ⟨h, hh⟩ ht).property

lemma answerCode_move {player : Bool} (σ : codeTree.Strategy player) {h : List ℕ}
    (hh : CodeLegal h) (ht : turn h = player) : MoveLegal h.length (answerCode σ h) := by
  have ha := answerCode_legal σ hh ht h.length (by simp)
  simpa using ha

/-- Retain both code moves after each bit supplied against I's coded strategy. -/
def firstHistory (σ : codeTree.Strategy true) (b : List Bool) : List ℕ :=
  b.foldl (fun h v => h ++ [answerCode σ h, bitCode v]) []

lemma firstHistory_append (σ : codeTree.Strategy true) (b : List Bool) (v : Bool) :
    firstHistory σ (b ++ [v]) = firstHistory σ b ++ [answerCode σ (firstHistory σ b), bitCode v] := by
  simp [firstHistory, List.foldl_append]

lemma firstHistory_spec (σ : codeTree.Strategy true) (b : List Bool) :
    CodeLegal (firstHistory σ b) ∧ (firstHistory σ b).length = 2 * b.length := by
  induction b using List.reverseRecOn with
  | nil => exact ⟨codeLegal_nil, rfl⟩
  | append_singleton b v ih =>
    have ht : turn (firstHistory σ b) = true := by simp [turn, ih.2]
    have hh := answerCode_legal σ ih.1 ht
    rw [firstHistory_append]
    constructor
    · have hm : MoveLegal (firstHistory σ b ++ [answerCode σ (firstHistory σ b)]).length (bitCode v) := by
        simp only [MoveLegal, List.length_append, List.length_singleton, ih.2]
        simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.reduceMod,
          Nat.one_ne_zero, ite_false]
        cases v <;> decide
      simpa only [List.append_assoc, List.singleton_append] using codeLegal_append hh hm
    · simp [ih.2]; omega

def firstLift (σ : codeTree.Strategy true) : FirstStrategy :=
  fun b => decodeWord (answerCode σ (firstHistory σ b))

lemma firstLift_code (σ : codeTree.Strategy true) (b : List Bool) :
    wordCode (firstLift σ b) = answerCode σ (firstHistory σ b) := by
  apply code_decodeWord
  have hs := firstHistory_spec σ b
  have hm := answerCode_move σ hs.1 (by simp [turn, hs.2])
  simpa only [MoveLegal, hs.2, Nat.mul_mod_right, ite_true] using hm

lemma firstLift_prefix (σ : codeTree.Strategy true) (b : Cantor) (n : ℕ) :
    seqPrefix (playWord (firstWords (firstLift σ) b) b) (2 * n) = firstHistory σ (seqPrefix b n) := by
  induction n with
  | zero => simp [seqPrefix, firstHistory]
  | succ n ih =>
    rw [playWord_prefix_succ, ih, seqPrefix_succ_eq_concat, firstHistory_append]
    simp only [firstWords, firstLift_code]

lemma firstLift_follows (σ : codeTree.Strategy true) (b : Cantor) :
    codeTree.Follows σ (codePlay (firstWords (firstLift σ) b) b) := by
  intro n ht
  have he : n % 2 = 0 := by simpa [turn] using ht
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  let p := codePlay (firstWords (firstLift σ) b) b
  have hh : (codeTree.prefixPosition p (2 * k)).val = firstHistory σ (seqPrefix b k) :=
    firstLift_prefix σ b k
  calc
    p.val (2 * k) = wordCode (firstLift σ (seqPrefix b k)) := by simp [p, codePlay, firstWords]
    _ = answerCode σ (firstHistory σ (seqPrefix b k)) := firstLift_code σ _
    _ = (σ (codeTree.prefixPosition p (2 * k)) ht).val := by
      rw [← hh]
      exact answerCode_position σ _ ht

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting coded $*$-game strategies
-/
lemma firstLift_winning {A : Set Cantor} {σ : codeTree.Strategy true}
    (hσ : codeTree.Winning (codePayoff A) true σ) : FirstWinning (firstLift σ) A := by
  intro b
  have h := hσ _ (firstLift_follows σ b)
  simpa [codePayoff, firstOutcome] using h


/-- Retain both code moves after each word supplied against II's coded strategy. -/
def secondHistory (τ : codeTree.Strategy false) (s : List (List Bool)) : List ℕ :=
  s.foldl (fun h t => h ++ [wordCode t, answerCode τ (h ++ [wordCode t])]) []

lemma secondHistory_append (τ : codeTree.Strategy false) (s : List (List Bool)) (t : List Bool) :
    secondHistory τ (s ++ [t]) = secondHistory τ s ++
      [wordCode t, answerCode τ (secondHistory τ s ++ [wordCode t])] := by
  simp [secondHistory, List.foldl_append]

lemma secondHistory_spec (τ : codeTree.Strategy false) (s : List (List Bool)) :
    CodeLegal (secondHistory τ s) ∧ (secondHistory τ s).length = 2 * s.length := by
  induction s using List.reverseRecOn with
  | nil => exact ⟨codeLegal_nil, rfl⟩
  | append_singleton s t ih =>
    have hw : MoveLegal (secondHistory τ s).length (wordCode t) := by
      rw [MoveLegal, ih.2, ite_eq_left (by omega)]
      exact mem_range_self t
    have hh := codeLegal_append ih.1 hw
    have ht : turn (secondHistory τ s ++ [wordCode t]) = false := by simp [turn, ih.2]
    rw [secondHistory_append]
    constructor
    · simpa only [List.append_assoc, List.singleton_append] using answerCode_legal τ hh ht
    · simp [ih.2]; omega

def secondLift (τ : codeTree.Strategy false) : SecondStrategy :=
  fun s t => decodeBit (answerCode τ (secondHistory τ s ++ [wordCode t]))

lemma secondLift_code (τ : codeTree.Strategy false) (s : List (List Bool)) (t : List Bool) :
    bitCode (secondLift τ s t) = answerCode τ (secondHistory τ s ++ [wordCode t]) := by
  apply code_decodeBit
  have hs := secondHistory_spec τ s
  have hw : MoveLegal (secondHistory τ s).length (wordCode t) := by
    rw [MoveLegal, hs.2, ite_eq_left (by omega)]
    exact mem_range_self t
  have hh := codeLegal_append hs.1 hw
  have ht : turn (secondHistory τ s ++ [wordCode t]) = false := by simp [turn, hs.2]
  have hm := answerCode_move τ hh ht
  simpa [MoveLegal, hs.2] using hm

lemma secondLift_prefix (τ : codeTree.Strategy false) (s : Words) (n : ℕ) :
    seqPrefix (playWord s (secondBits (secondLift τ) s)) (2 * n) = secondHistory τ (seqPrefix s n) := by
  induction n with
  | zero => simp [seqPrefix, secondHistory]
  | succ n ih =>
    rw [playWord_prefix_succ, ih, seqPrefix_succ_eq_concat, secondHistory_append]
    simp only [secondBits, secondLift_code]

lemma secondLift_follows (τ : codeTree.Strategy false) (s : Words) :
    codeTree.Follows τ (codePlay s (secondBits (secondLift τ) s)) := by
  intro n ht
  have he : n % 2 ≠ 0 := by simpa [turn] using ht
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  let p := codePlay s (secondBits (secondLift τ) s)
  have hh : (codeTree.prefixPosition p (2 * k + 1)).val =
      secondHistory τ (seqPrefix s k) ++ [wordCode (s k)] := by
    change seqPrefix (playWord s (secondBits (secondLift τ) s)) (2 * k + 1) = _
    rw [seqPrefix_succ_eq_concat, secondLift_prefix, playWord_even]
  calc
    p.val (2 * k + 1) = bitCode (secondLift τ (seqPrefix s k) (s k)) := by
      simp [p, codePlay, secondBits]
    _ = answerCode τ (secondHistory τ (seqPrefix s k) ++ [wordCode (s k)]) := secondLift_code τ _ _
    _ = (τ (codeTree.prefixPosition p (2 * k + 1)) ht).val := by
      rw [← hh]
      exact answerCode_position τ _ ht

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting coded $*$-game strategies
-/
lemma secondLift_winning {A : Set Cantor} {τ : codeTree.Strategy false}
    (hτ : codeTree.Winning (codePayoff A) false τ) : SecondWinning (secondLift τ) A := by
  intro s
  have h := hτ _ (secondLift_follows τ s)
  simpa [codePayoff, secondOutcome] using h

/-- A coded winning strategy supplies the corresponding strategy in the star game. -/
theorem determined_of_code_determined {A : Set Cantor} (h : codeTree.Determined (codePayoff A)) :
    (∃ σ, FirstWinning σ A) ∨ ∃ τ, SecondWinning τ A := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · exact Or.inl ⟨firstLift σ, firstLift_winning hσ⟩
  · exact Or.inr ⟨secondLift τ, secondLift_winning hτ⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The Polish branch space and continuous map above give $\pi^{-1}(A)\in\Gamma$. Thus the coded game is determined.
    Lifting its winning strategy gives a winning strategy for the same player in the $*$-game on $A$.
    Davis's theorem now gives the asserted alternative.
    \end{proof}
-/
/-- Pull back the payoff along the continuous outcome map, then use Davis's theorem. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Perfect-set regularity from determinacy
-/
theorem pointclass_determinacy_perfect_set
    (Γ : (Y : Type) → TopologicalSpace Y → Set Y → Prop)
    (hpull : ∀ {Y Z : Type} [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]
      [PolishSpace Y] [PolishSpace Z] {f : Y → Z} {A : Set Z},
      Continuous f → Γ Z tZ A → Γ Y tY (f ⁻¹' A))
    (hdet : ∀ (T : TreeGames.GameTree ℕ) (A : Set T.Play),
      Γ T.Play inferInstance A → T.Determined A)
    {A : Set Cantor} (hA : Γ Cantor inferInstance A) :
    A.Countable ∨ ∃ f : Cantor → Cantor, IsClosedEmbedding f ∧ range f ⊆ A := by
  apply perfect_set_alternative
  apply determined_of_code_determined
  exact hdet codeTree (codePayoff A) (hpull codeOutcome_continuous hA)

end PolishSpaceBook.DavisStarGame
