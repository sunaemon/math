module

public import PolishSpaceBook.BanachMazurStrategyCoding

@[expose] public section

/-!
# Lifting basis strategies to arbitrary open moves

The finite simulation stores codes, including the strategy's own chosen codes.
Total fallbacks only define responses away from compatible histories; induction
shows that a legal play always follows the simulated coded strategy.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Metric Topology
open scoped Classical
variable {X : Type*} [MetricSpace X]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Use the fixed refinements $\rho_n(U)$ from the preceding proof. Retain the entire simulated code history:
    distinct codes may denote the same open set, and the coded strategy can distinguish them.

    Suppose II has a winning coded strategy $\tau$. Start with $s_0:=\emptyset$. After I's arbitrary open move
    $U_n$, set
    $$
    \begin{aligned}
    a_n&:=\rho_n(U_n),& b_n&:=\tau(s_n\concat(a_n)),\\
    V_n&:=B_{b_n},& s_{n+1}&:=s_n\concat(a_n,b_n).
    \end{aligned}
    $$
    Thus $s_n$ records all earlier simulated moves. The first refined opening lies in $W$. At later rounds,
    $$\Closure{B_{a_n}}\IncludedIn U_n\IncludedIn V_{n-1}=B_{b_{n-1}}\qquad(n>0).$$
    Induction therefore makes the simulated opening legal. The coded response satisfies
    $$\Closure{V_n}\IncludedIn B_{a_n}\IncludedIn U_n,\qquad \Diameter{V_n}\le 2^{-n},$$
    so it is also a legal open response. The coded and open plays have exactly the same II-responses $V_n$,
    hence the same unique outcome. Since $\tau$ wins, that outcome is outside $A$.

    Suppose instead that I has a winning coded strategy $\sigma$. Play its initial code as an open set:
    $$a_0:=\sigma(\emptyset),\qquad U_0:=B_{a_0},\qquad s_0:=(a_0).$$
    After II's arbitrary open response $V_n$, put
    $$
    \begin{aligned}
    b_n&:=\rho_n(V_n),& a_{n+1}&:=\sigma(s_n\concat(b_n)),\\
    U_{n+1}&:=B_{a_{n+1}},& s_{n+1}&:=s_n\concat(b_n,a_{n+1}).
    \end{aligned}
    $$
    Here $s_n$ ends with I's current code. The simulated II-response is legal because
    $$\Closure{B_{b_n}}\IncludedIn V_n\IncludedIn U_n,\qquad \Diameter{B_{b_n}}\le 2^{-n}.$$
    The prescribed next move satisfies
    $$\Closure{U_{n+1}}\IncludedIn B_{b_n}\IncludedIn V_n,$$
    so the actual open play is legal as well. The coded outcome $x$ lies in every
    $\Closure{B_{b_n}}\IncludedIn V_n$, hence is the unique outcome of the actual open play. Since $\sigma$ wins,
    $x\in A$. Both constructions use only the current move and the retained finite history, so they define strategies.
    \end{proof}
-/
/-- Extend a code strategy to all finite words; the fallback is never used in a legal simulation. -/
def answerCode (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) (s : List ℕ) : ℕ :=
  if h : s ∈ (codeTree B W).nodes ∧ TreeGames.GameTree.turn s = player then
    (τ ⟨s, h.1⟩ h.2).val
  else 0

lemma answerCode_eq (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) (s : (codeTree B W).Position)
    (hs : TreeGames.GameTree.turn s.val = player) :
    answerCode B W τ s.val = (τ s hs).val := by
  have h : s.val ∈ (codeTree B W).nodes ∧ TreeGames.GameTree.turn s.val = player := ⟨s.property, hs⟩
  simp only [answerCode, dite_eq_left h]

lemma answerCode_legal (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) {s : List ℕ} (hs : CodeLegal B W.openSet s)
    (ht : TreeGames.GameTree.turn s = player) :
    CodeLegal B W.openSet (s ++ [answerCode B W τ s]) := by
  rw [answerCode_eq B W τ ⟨s, hs⟩ ht]
  exact (τ ⟨s, hs⟩ ht).property

/-- One opponent refinement followed by the prescribed coded response. -/
def liftStep (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) (s : List ℕ) (U : Move X) : List ℕ :=
  let a := B.refinement U (s.length / 2)
  s ++ [a, answerCode B W τ (s ++ [a])]

/-- Replay the entire finite opponent history, retaining the codes selected along the way. -/
def liftHistory (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) (start : List ℕ) (h : List (Move X)) : List ℕ :=
  h.foldl (liftStep B W τ) start

lemma liftHistory_length (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) (start : List ℕ) (h : List (Move X)) :
    (liftHistory B W τ start h).length = start.length + 2 * h.length := by
  induction h generalizing start with
  | nil => simp [liftHistory]
  | cons U h ih =>
    change (liftHistory B W τ (liftStep B W τ start U) h).length = _
    rw [ih]
    simp [liftStep]
    omega

lemma liftHistory_append (B : CodeBasis X) (W : Move X) {player : Bool}
    (τ : (codeTree B W).Strategy player) (start : List ℕ) (h : List (Move X)) (U : Move X) :
    liftHistory B W τ start (h ++ [U]) = liftStep B W τ (liftHistory B W τ start h) U := by
  simp [liftHistory, List.foldl_append]

lemma codeLegal_last_step (B : CodeBasis X) (W : Set X) {s : List ℕ} {a : ℕ}
    (hs : CodeLegal B W (s ++ [a])) (hne : s.length ≠ 0) :
    closure (B.move a).openSet ⊆ (B.move s[s.length - 1]!).openSet := by
  have h := hs.1 s.length (by simp)
  rw [dite_eq_right hne] at h
  simpa only [List.getElem_concat_length rfl,
    List.getElem_append_left (show s.length - 1 < s.length by omega),
    getElem!_pos s (s.length - 1) (by omega)] using h

lemma codeLegal_last_bound (B : CodeBasis X) (W : Set X) {s : List ℕ} {a : ℕ}
    (hs : CodeLegal B W (s ++ [a])) (hodd : s.length % 2 = 1) :
    Bornology.IsBounded (B.move a).openSet ∧
      diam (B.move a).openSet ≤ (1 / 2 : ℝ) ^ (s.length / 2) := by
  have h := hs.2 s.length (by simp) hodd
  simpa using h

/-- The code prescribed for II after the given open history and current move. -/
def secondLiftCode (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (h : List (Move X)) (U : Move X) : ℕ :=
  answerCode B W τ (liftHistory B W τ [] h ++ [B.refinement U h.length])

/-- A prescribed basic response is legal as an open response at the current round. -/
def FitsResponse (B : CodeBasis X) (n : ℕ) (U : Move X) (a : ℕ) : Prop :=
  closure (B.move a).openSet ⊆ U.openSet ∧ Bornology.IsBounded (B.move a).openSet ∧
    diam (B.move a).openSet ≤ (1 / 2 : ℝ) ^ n

/-- Outside compatible histories use a small ball; on a legal play use the coded response unchanged. -/
def liftedSecondStrategy (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false) :
    Strategy X := fun h U =>
  if good : FitsResponse B h.length U (secondLiftCode B W τ h U) then
    { toMove := B.move (secondLiftCode B W τ h U)
      closure_subset := good.1
      bounded := good.2.1
      diam_le := good.2.2 }
  else smallResponse h.length U

lemma liftedSecond_eq (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (h : List (Move X)) (U : Move X) (good : FitsResponse B h.length U (secondLiftCode B W τ h U)) :
    (liftedSecondStrategy B W τ h U).openSet = (B.move (secondLiftCode B W τ h U)).openSet := by
  simp only [liftedSecondStrategy, dite_eq_left good]

/-- Legality of the simulated opening move forces the next two codes and the actual response to agree. -/
lemma secondLift_round (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (h : List (Move X)) (U : Move X)
    (hs : CodeLegal B W.openSet (liftHistory B W τ [] h ++ [B.refinement U h.length])) :
    CodeLegal B W.openSet (liftHistory B W τ [] (h ++ [U])) ∧
      FitsResponse B h.length U (secondLiftCode B W τ h U) := by
  let s := liftHistory B W τ [] h ++ [B.refinement U h.length]
  have hlen : s.length = 2 * h.length + 1 := by simp [s, liftHistory_length]
  have ht : TreeGames.GameTree.turn s = false := by simp [TreeGames.GameTree.turn, hlen]
  have hb := answerCode_legal B W τ hs ht
  have hstep : closure (B.move (answerCode B W τ s)).openSet ⊆
      (B.move (B.refinement U h.length)).openSet := by
    simpa [s] using codeLegal_last_step B W.openSet hb (by change s.length ≠ 0; omega)
  have hsub := hstep.trans (subset_closure.trans (B.refinement_spec U h.length).1)
  have hbound := codeLegal_last_bound B W.openSet hb (by change s.length % 2 = 1; omega)
  constructor
  · simpa [liftHistory_append, liftStep, liftHistory_length, s, List.append_assoc] using hb
  · refine ⟨?_, ?_⟩
    · simpa [s, secondLiftCode] using hsub
    · simpa [hlen, secondLiftCode, s, show (2 * h.length + 1) / 2 = h.length by omega] using hbound


lemma secondLift_history_succ (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (n : ℕ) :
    liftHistory B W τ [] ((List.range (n + 1)).map p) =
      liftHistory B W τ [] ((List.range n).map p) ++
        [B.refinement (p n) n, secondLiftCode B W τ ((List.range n).map p) (p n)] := by
  simp [List.range_succ, List.map_append, liftHistory_append, liftStep, liftHistory_length, secondLiftCode]

lemma secondLift_compatible (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (hp : Legal W.openSet (liftedSecondStrategy B W τ) p) (n : ℕ) :
    CodeLegal B W.openSet
        (liftHistory B W τ [] ((List.range n).map p) ++ [B.refinement (p n) n]) ∧
      FitsResponse B n (p n) (secondLiftCode B W τ ((List.range n).map p) (p n)) := by
  have step (k : ℕ)
      (h : CodeLegal B W.openSet
        (liftHistory B W τ [] ((List.range k).map p) ++ [B.refinement (p k) k])) :
      FitsResponse B k (p k) (secondLiftCode B W τ ((List.range k).map p) (p k)) := by
    simpa using (secondLift_round B W τ ((List.range k).map p) (p k) (by simpa using h)).2
  induction n with
  | zero =>
    have h : CodeLegal B W.openSet
        (liftHistory B W τ [] ((List.range 0).map p) ++ [B.refinement (p 0) 0]) := by
      apply codeLegal_append B W.openSet (codeLegal_nil B W.openSet)
      · exact (subset_closure.trans (B.refinement_spec (p 0) 0).1).trans hp.1
      · simp
    exact ⟨h, step 0 h⟩
  | succ n ih =>
    have hprev := (secondLift_round B W τ ((List.range n).map p) (p n) (by simpa using ih.1)).1
    have hs : CodeLegal B W.openSet (liftHistory B W τ [] ((List.range (n + 1)).map p)) := by
      simpa [List.range_succ, List.map_append] using hprev
    have hv : (responseAt (liftedSecondStrategy B W τ) p n).openSet =
        (B.move (secondLiftCode B W τ ((List.range n).map p) (p n))).openSet :=
      liftedSecond_eq B W τ _ _ (by simpa using ih.2)
    have hlast :
        (liftHistory B W τ [] ((List.range (n + 1)).map p))[
          (liftHistory B W τ [] ((List.range (n + 1)).map p)).length - 1]! =
          secondLiftCode B W τ ((List.range n).map p) (p n) := by
      rw [secondLift_history_succ]
      simp
    have hnew : CodeLegal B W.openSet
        (liftHistory B W τ [] ((List.range (n + 1)).map p) ++ [B.refinement (p (n + 1)) (n + 1)]) := by
      apply codeLegal_append B W.openSet hs
      · rw [dite_eq_right (by simp [liftHistory_length])]
        rw [← getElem!_pos _ _ (by simp [liftHistory_length])]
        rw [hlast, ← hv]
        exact (B.refinement_spec (p (n + 1)) (n + 1)).1.trans (subset_closure.trans (hp.2 n))
      · simp [liftHistory_length]
    exact ⟨hnew, step (n + 1) hnew⟩

/-- The infinite code word produced by the retained finite histories. -/
def secondLiftWord (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (i : ℕ) : ℕ :=
  if i % 2 = 0 then B.refinement (p (i / 2)) (i / 2)
  else secondLiftCode B W τ ((List.range (i / 2)).map p) (p (i / 2))

lemma secondLiftWord_even (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (n : ℕ) :
    secondLiftWord B W τ p (2 * n) = B.refinement (p n) n := by simp [secondLiftWord]

lemma secondLiftWord_odd (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (n : ℕ) :
    secondLiftWord B W τ p (2 * n + 1) = secondLiftCode B W τ ((List.range n).map p) (p n) := by
  simp [secondLiftWord, show (2 * n + 1) / 2 = n by omega]

lemma secondLiftWord_prefix (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (n : ℕ) :
    seqPrefix (secondLiftWord B W τ p) (2 * n) = liftHistory B W τ [] ((List.range n).map p) := by
  induction n with
  | zero => simp [liftHistory, seqPrefix]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, seqPrefix_succ_eq_concat,
      seqPrefix_succ_eq_concat, ih, secondLiftWord_even, secondLiftWord_odd, secondLift_history_succ]
    simp [List.append_assoc]

lemma secondLiftWord_legal (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (hp : Legal W.openSet (liftedSecondStrategy B W τ) p) :
    secondLiftWord B W τ p ∈ treeBody (codeTree B W).nodes := by
  intro n
  have hc := (secondLift_compatible B W τ p hp n).1
  have he : seqPrefix (secondLiftWord B W τ p) (2 * n + 1) =
      liftHistory B W τ [] ((List.range n).map p) ++ [B.refinement (p n) n] := by
    rw [seqPrefix_succ_eq_concat, secondLiftWord_prefix, secondLiftWord_even]
  rw [← he] at hc
  exact codeLegal_prefix B W.openSet hc (seqPrefix_prefixOf_of_le _ (by omega))

def secondLiftPlay (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (hp : Legal W.openSet (liftedSecondStrategy B W τ) p) : (codeTree B W).Play :=
  ⟨secondLiftWord B W τ p, secondLiftWord_legal B W τ p hp⟩

lemma secondLiftPlay_follows (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (hp : Legal W.openSet (liftedSecondStrategy B W τ) p) :
    (codeTree B W).Follows τ (secondLiftPlay B W τ p hp) := by
  intro i hi
  have hodd : i % 2 = 1 := by
    simp only [TreeGames.GameTree.turn, seqPrefix, List.length_ofFn, beq_eq_false_iff_ne] at hi
    omega
  obtain ⟨n, rfl⟩ : ∃ n, i = 2 * n + 1 := ⟨i / 2, by omega⟩
  rw [← answerCode_eq B W τ _ hi]
  change secondLiftWord B W τ p (2 * n + 1) =
    answerCode B W τ (seqPrefix (secondLiftWord B W τ p) (2 * n + 1))
  rw [seqPrefix_succ_eq_concat, secondLiftWord_prefix, secondLiftWord_even, secondLiftWord_odd]
  simp only [secondLiftCode, List.length_map, List.length_range]

lemma secondLift_response (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy false)
    (p : ℕ → Move X) (hp : Legal W.openSet (liftedSecondStrategy B W τ) p) (n : ℕ) :
    (responseAt (liftedSecondStrategy B W τ) p n).openSet =
      (codeMove B W (secondLiftPlay B W τ p hp) (2 * n + 1)).openSet := by
  change (liftedSecondStrategy B W τ ((List.range n).map p) (p n)).openSet =
    (B.move (secondLiftWord B W τ p (2 * n + 1))).openSet
  rw [secondLiftWord_odd]
  exact liftedSecond_eq B W τ _ _ (by simpa using (secondLift_compatible B W τ p hp n).2)

theorem liftedSecond_winning [CompleteSpace X] (B : CodeBasis X) (W : Move X) {A : Set X}
    (τ : (codeTree B W).Strategy false) (hτ : (codeTree B W).Winning (codePayoff B W A) false τ) :
    Winning A W.openSet (liftedSecondStrategy B W τ) := by
  intro p hp
  refine ⟨codeOutcome B W (secondLiftPlay B W τ p hp), ?_, ?_⟩
  · intro n
    rw [secondLift_response B W τ p hp n]
    exact codeOutcome_mem_closure B W _ n
  · exact hτ _ (secondLiftPlay_follows B W τ p hp)


/-- I begins with the exact code prescribed at the root. -/
def firstLiftInitial (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true) : ℕ :=
  answerCode B W τ []

lemma firstLiftInitial_legal (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true) :
    CodeLegal B W.openSet [firstLiftInitial B W τ] :=
  answerCode_legal B W τ (codeLegal_nil B W.openSet) (by simp [TreeGames.GameTree.turn])

lemma firstLiftInitial_subset (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true) :
    (B.move (firstLiftInitial B W τ)).openSet ⊆ W.openSet := by
  have h := (firstLiftInitial_legal B W τ).1 0 (by simp)
  simpa using h

/-- Prescribe the next I-code after refining the current arbitrary II-move. -/
def firstLiftCode (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (h : List (Move X)) (V : Move X) : ℕ :=
  answerCode B W τ (liftHistory B W τ [firstLiftInitial B W τ] h ++ [B.refinement V h.length])

def liftedFirstStrategy (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true) :
    FirstStrategy X where
  first := B.move (firstLiftInitial B W τ)
  reply := fun h V =>
    if good : closure (B.move (firstLiftCode B W τ h V)).openSet ⊆ V.openSet then
      { toMove := B.move (firstLiftCode B W τ h V), closure_subset := good }
    else
      { toMove := (smallResponse h.length V).toMove
        closure_subset := (smallResponse h.length V).closure_subset }

lemma liftedFirst_eq (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (h : List (Move X)) (V : Move X)
    (good : closure (B.move (firstLiftCode B W τ h V)).openSet ⊆ V.openSet) :
    ((liftedFirstStrategy B W τ).reply h V).openSet = (B.move (firstLiftCode B W τ h V)).openSet := by
  simp only [liftedFirstStrategy, dite_eq_left good]

lemma firstLift_round (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (h : List (Move X)) (V : Move X)
    (hs : CodeLegal B W.openSet
      (liftHistory B W τ [firstLiftInitial B W τ] h ++ [B.refinement V h.length])) :
    CodeLegal B W.openSet (liftHistory B W τ [firstLiftInitial B W τ] (h ++ [V])) ∧
      closure (B.move (firstLiftCode B W τ h V)).openSet ⊆ V.openSet := by
  let s := liftHistory B W τ [firstLiftInitial B W τ] h ++ [B.refinement V h.length]
  have hlen : s.length = 2 * h.length + 2 := by simp [s, liftHistory_length]; omega
  have ht : TreeGames.GameTree.turn s = true := by simp [TreeGames.GameTree.turn, hlen]
  have hb := answerCode_legal B W τ hs ht
  have hstep : closure (B.move (answerCode B W τ s)).openSet ⊆
      (B.move (B.refinement V h.length)).openSet := by
    simpa [s] using codeLegal_last_step B W.openSet hb (by change s.length ≠ 0; omega)
  constructor
  · simpa [liftHistory_append, liftStep, liftHistory_length, s, List.append_assoc,
      show (1 + 2 * h.length) / 2 = h.length by omega] using hb
  · exact hstep.trans (subset_closure.trans (B.refinement_spec V h.length).1)

lemma firstLift_history_succ (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (n : ℕ) :
    liftHistory B W τ [firstLiftInitial B W τ] ((List.range (n + 1)).map q) =
      liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q) ++
        [B.refinement (q n) n, firstLiftCode B W τ ((List.range n).map q) (q n)] := by
  simp [List.range_succ, List.map_append, liftHistory_append, liftStep, liftHistory_length, firstLiftCode,
    show (1 + 2 * n) / 2 = n by omega]

lemma firstLift_compatible (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (hq : FirstLegal (liftedFirstStrategy B W τ) q) (n : ℕ) :
    CodeLegal B W.openSet (liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q)) ∧
      (firstMoveAt (liftedFirstStrategy B W τ) q n).openSet =
        (B.move (liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q))[
          (liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q)).length - 1]!).openSet := by
  induction n with
  | zero =>
    constructor
    · simpa [liftHistory] using firstLiftInitial_legal B W τ
    · simp [liftHistory, firstMoveAt, liftedFirstStrategy]
  | succ n ih =>
    let h := (List.range n).map q
    let s := liftHistory B W τ [firstLiftInitial B W τ] h
    have hlen : s.length = 1 + 2 * n := by simp [s, h, liftHistory_length]
    have hopen : CodeLegal B W.openSet (s ++ [B.refinement (q n) n]) := by
      apply codeLegal_append B W.openSet (show CodeLegal B W.openSet s from ih.1)
      · rw [dite_eq_right (by omega)]
        rw [← getElem!_pos s (s.length - 1) (by omega)]
        rw [← ih.2]
        exact (B.refinement_spec (q n) n).1.trans (subset_closure.trans (hq n).1)
      · intro _
        simpa only [hlen, show (1 + 2 * n) / 2 = n by omega] using (B.refinement_spec (q n) n).2
    have hr := firstLift_round B W τ h (q n) (by simpa [h] using hopen)
    constructor
    · simpa [h, List.range_succ, List.map_append] using hr.1
    · rw [firstLift_history_succ]
      simp only [firstMoveAt]
      rw [liftedFirst_eq B W τ h (q n) hr.2]
      simp [h]

/-- Interleave the retained I-codes and the refinements of II's actual moves. -/
def firstLiftWord (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (i : ℕ) : ℕ :=
  if i % 2 = 0 then
    let s := liftHistory B W τ [firstLiftInitial B W τ] ((List.range (i / 2)).map q)
    s[s.length - 1]!
  else B.refinement (q (i / 2)) (i / 2)

lemma firstLiftWord_even (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (n : ℕ) :
    firstLiftWord B W τ q (2 * n) =
      (liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q))[
        (liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q)).length - 1]! := by
  simp [firstLiftWord]

lemma firstLiftWord_odd (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (n : ℕ) :
    firstLiftWord B W τ q (2 * n + 1) = B.refinement (q n) n := by
  simp [firstLiftWord, show (2 * n + 1) / 2 = n by omega]

lemma firstLiftWord_next (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (n : ℕ) :
    firstLiftWord B W τ q (2 * (n + 1)) = firstLiftCode B W τ ((List.range n).map q) (q n) := by
  rw [firstLiftWord_even, firstLift_history_succ]
  simp

lemma firstLiftWord_prefix (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (n : ℕ) :
    seqPrefix (firstLiftWord B W τ q) (2 * n + 1) =
      liftHistory B W τ [firstLiftInitial B W τ] ((List.range n).map q) := by
  induction n with
  | zero => simp [seqPrefix, firstLiftWord, liftHistory]
  | succ n ih =>
    rw [seqPrefix_succ_eq_concat, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      seqPrefix_succ_eq_concat, ih, firstLiftWord_odd,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega, firstLiftWord_next, firstLift_history_succ]
    simp [List.append_assoc]

lemma firstLiftWord_legal (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (hq : FirstLegal (liftedFirstStrategy B W τ) q) :
    firstLiftWord B W τ q ∈ treeBody (codeTree B W).nodes := by
  intro n
  have hc := (firstLift_compatible B W τ q hq n).1
  rw [← firstLiftWord_prefix] at hc
  exact codeLegal_prefix B W.openSet hc (seqPrefix_prefixOf_of_le _ (by omega))

def firstLiftPlay (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (hq : FirstLegal (liftedFirstStrategy B W τ) q) : (codeTree B W).Play :=
  ⟨firstLiftWord B W τ q, firstLiftWord_legal B W τ q hq⟩

lemma firstLiftPlay_follows (B : CodeBasis X) (W : Move X) (τ : (codeTree B W).Strategy true)
    (q : ℕ → Move X) (hq : FirstLegal (liftedFirstStrategy B W τ) q) :
    (codeTree B W).Follows τ (firstLiftPlay B W τ q hq) := by
  intro i hi
  have heven : i % 2 = 0 := by
    simpa only [TreeGames.GameTree.turn, seqPrefix, List.length_ofFn, beq_iff_eq] using hi
  obtain ⟨n, rfl⟩ : ∃ n, i = 2 * n := ⟨i / 2, by omega⟩
  rw [← answerCode_eq B W τ _ hi]
  change firstLiftWord B W τ q (2 * n) =
    answerCode B W τ (seqPrefix (firstLiftWord B W τ q) (2 * n))
  cases n with
  | zero => simp [firstLiftWord, liftHistory, seqPrefix, firstLiftInitial]
  | succ n =>
    rw [firstLiftWord_next, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      seqPrefix_succ_eq_concat, firstLiftWord_prefix, firstLiftWord_odd]
    simp only [firstLiftCode, List.length_map, List.length_range]

theorem liftedFirst_winning [CompleteSpace X] (B : CodeBasis X) (W : Move X) {A : Set X}
    (τ : (codeTree B W).Strategy true) (hτ : (codeTree B W).Winning (codePayoff B W A) true τ) :
    FirstWinning A W.openSet (liftedFirstStrategy B W τ) := by
  refine ⟨firstLiftInitial_subset B W τ, fun q hq => ?_⟩
  refine ⟨codeOutcome B W (firstLiftPlay B W τ q hq), ?_, ?_⟩
  · intro n
    have hx := codeOutcome_mem_closure B W (firstLiftPlay B W τ q hq) n
    change _ ∈ closure (B.move (firstLiftWord B W τ q (2 * n + 1))).openSet at hx
    rw [firstLiftWord_odd] at hx
    exact subset_closure ((B.refinement_spec (q n) n).1 hx)
  · exact hτ _ (firstLiftPlay_follows B W τ q hq)


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting coded strategies
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: corollary
  title: Coding equivalence
-/
theorem firstWinning_iff_codeWinning [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) :
    (∃ σ : FirstStrategy X, FirstWinning A W.openSet σ) ↔
      ∃ τ : (codeTree B W).Strategy true, (codeTree B W).Winning (codePayoff B W A) true τ := by
  constructor
  · exact (winning_transfers_to_code B W A).1
  · rintro ⟨τ, hτ⟩
    exact ⟨liftedFirstStrategy B W τ, liftedFirst_winning B W τ hτ⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: corollary
  title: Coding equivalence
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting coded strategies
-/
theorem secondWinning_iff_codeWinning [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) :
    (∃ σ : Strategy X, Winning A W.openSet σ) ↔
      ∃ τ : (codeTree B W).Strategy false, (codeTree B W).Winning (codePayoff B W A) false τ := by
  constructor
  · exact (winning_transfers_to_code B W A).2
  · rintro ⟨τ, hτ⟩
    exact ⟨liftedSecondStrategy B W τ, liftedSecond_winning B W τ hτ⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: corollary
  title: Coding equivalence
-/
theorem code_determined_iff [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) :
    (codeTree B W).Determined (codePayoff B W A) ↔
      (∃ σ : FirstStrategy X, FirstWinning A W.openSet σ) ∨ ∃ σ : Strategy X, Winning A W.openSet σ :=
  or_congr (firstWinning_iff_codeWinning B W A).symm (secondWinning_iff_codeWinning B W A).symm

end PolishSpaceBook.BanachMazurGame
