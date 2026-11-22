module

public import PolishSpaceBook.BanachMazurCoding
public import PolishSpaceBook.BanachMazurFirstPlayer

@[expose] public section

/-!
# Moving open-set strategies to the countable basis

Refine a prescribed move inside its open set, retaining the simulated opponent's
entire history. The two nested plays have the same outcome.
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
    For every nonempty open $U$ and every $n$, fix a code $\rho_n(U)$ such that
    $$\Closure{B_{\rho_n(U)}}\IncludedIn U,\qquad \Diameter{B_{\rho_n(U)}}\le 2^{-n}.$$
    These choices depend only on $U$ and $n$ and will be used throughout the simulation.

    Suppose first that I has a winning strategy. When it prescribes an open move $U_n$, play the code
    $\rho_0(U_n)$ instead. Feed II's actual basic responses $V_0,\ldots,V_n$ to the original strategy to obtain
    its next prescribed move. This preserves the entire history of II's moves. Writing
    $\widetilde U_n:=B_{\rho_0(U_n)}$, the relevant inclusions are
    $$
    \Closure{V_n}\IncludedIn\widetilde U_n\IncludedIn U_n,\qquad
    \Closure{\widetilde U_{n+1}}\IncludedIn U_{n+1}\IncludedIn V_n.
    $$
    The initial refinement is contained in $W$, so the coded strategy is legal. The same II-responses form a
    legal play against the original strategy. Both outcomes are the unique point of
    $\bigcap_n\Closure{V_n}$, and hence belong to $A$.

    Now suppose that II has a winning strategy. Decode I's basic moves $U_0,\ldots,U_n$, let the original
    strategy prescribe $V_n$, and answer with the code $\rho_n(V_n)$. Put
    $\widetilde V_n:=B_{\rho_n(V_n)}$. Then
    $$
    \Closure{\widetilde V_n}\IncludedIn V_n\IncludedIn U_n,\qquad
    \Diameter{\widetilde V_n}\le 2^{-n},\qquad
    \Closure{U_{n+1}}\IncludedIn\widetilde V_n\IncludedIn V_n.
    $$
    Thus the coded response is legal, and the decoded I-moves are legal against the original strategy.
    The coded outcome $x$ lies in every $\Closure{\widetilde V_n}$ and therefore in every $\Closure{V_n}$.
    Uniqueness of the original outcome identifies it with $x$, so $x\notin A$.
    \end{proof}
-/
/-- Fix a small basic refinement for every open move and round. -/
def CodeBasis.refinement (B : CodeBasis X) (U : Move X) (n : ℕ) : ℕ :=
  (B.exists_small U n).choose

lemma CodeBasis.refinement_spec (B : CodeBasis X) (U : Move X) (n : ℕ) :
    closure (B.move (B.refinement U n)).openSet ⊆ U.openSet ∧
      Bornology.IsBounded (B.move (B.refinement U n)).openSet ∧
      diam (B.move (B.refinement U n)).openSet ≤ (1 / 2 : ℝ) ^ n :=
  (B.exists_small U n).choose_spec

/-- Decode the indicated player's first `n` moves, preserving their order. -/
def decodedHistory (B : CodeBasis X) (s : List ℕ) (parity n : ℕ) : List (Move X) :=
  (List.range n).map fun i => B.move s[2 * i + parity]!

lemma decodedHistory_prefix (B : CodeBasis X) (p : ℕ → ℕ) (m parity n : ℕ)
    (h : ∀ i < n, 2 * i + parity < m) :
    decodedHistory B (seqPrefix p m) parity n =
      (List.range n).map (fun i => B.move (p (2 * i + parity))) := by
  apply List.map_congr_left
  intro i hi
  have hlt : 2 * i + parity < (seqPrefix p m).length := by
    simpa using h i (List.mem_range.mp hi)
  rw [getElem!_pos (seqPrefix p m) (2 * i + parity) hlt]
  simp only [seqPrefix, List.getElem_ofFn]

/-- II refines the response of the original strategy, after decoding I's moves. -/
def codedSecondStrategy (B : CodeBasis X) (W : Move X) (σ : Strategy X) :
    (codeTree B W).Strategy false := fun s hs => by
  have hodd : s.val.length % 2 = 1 := by
    have h := hs
    simp only [TreeGames.GameTree.turn, beq_eq_false_iff_ne] at h
    omega
  have hpos : 0 < s.val.length := by omega
  let U := B.move s.val[s.val.length - 1]!
  let h := decodedHistory B s.val 0 (s.val.length / 2)
  let V := σ h U
  let a := B.refinement V.toMove (s.val.length / 2)
  refine ⟨a, codeLegal_append B W.openSet s.property ?_ ?_⟩
  · rw [dite_eq_right (by omega)]
    simpa only [U, getElem!_pos s.val (s.val.length - 1) (show s.val.length - 1 < s.val.length by omega)] using
      (B.refinement_spec V.toMove (s.val.length / 2)).1.trans (subset_closure.trans V.closure_subset)
  · intro _
    exact (B.refinement_spec V.toMove _).2

lemma codedSecondStrategy_response (B : CodeBasis X) (W : Move X) (σ : Strategy X)
    (p : (codeTree B W).Play) (hp : (codeTree B W).Follows (codedSecondStrategy B W σ) p)
    (n : ℕ) :
    closure (codeMove B W p (2 * n + 1)).openSet ⊆
      (responseAt σ (fun i => codeMove B W p (2 * i)) n).openSet := by
  have hturn : TreeGames.GameTree.turn (seqPrefix p.val (2 * n + 1)) = false := by
    simp [TreeGames.GameTree.turn]
  have he := hp (2 * n + 1) hturn
  have hh := decodedHistory_prefix B p.val (2 * n + 1) 0 n (by intro i hi; omega)
  have hlen : (seqPrefix p.val (2 * n + 1)).length / 2 = n := by simp; omega
  have hlast : (seqPrefix p.val (2 * n + 1))[(seqPrefix p.val (2 * n + 1)).length - 1]! =
      p.val (2 * n) := by
    rw [getElem!_pos (seqPrefix p.val (2 * n + 1)) _ (by simp)]
    simp only [seqPrefix, List.length_ofFn, List.getElem_ofFn, Nat.add_sub_cancel]
  change p.val (2 * n + 1) = B.refinement _ _ at he
  change closure (B.move (p.val (2 * n + 1))).openSet ⊆ _
  rw [he]
  apply (B.refinement_spec _ _).1.trans
  dsimp only [TreeGames.GameTree.prefixPosition]
  rw [hlen, hh, hlast]
  exact Subset.rfl

lemma decodedSecond_legal (B : CodeBasis X) (W : Move X) (σ : Strategy X)
    (p : (codeTree B W).Play) (hp : (codeTree B W).Follows (codedSecondStrategy B W σ) p) :
    Legal W.openSet σ (fun i => codeMove B W p (2 * i)) := by
  refine ⟨by simpa using codeMove_initial B W p, fun n => ?_⟩
  have h := (codeMove_step B W p (2 * n + 1)).trans
    (subset_closure.trans (codedSecondStrategy_response B W σ p hp n))
  convert h using 1

lemma codedSecond_outcome [CompleteSpace X] (B : CodeBasis X) (W : Move X) (σ : Strategy X)
    (p : (codeTree B W).Play) (hp : (codeTree B W).Follows (codedSecondStrategy B W σ) p) :
    IsOutcome σ (fun i => codeMove B W p (2 * i)) (codeOutcome B W p) := by
  intro n
  exact subset_closure (codedSecondStrategy_response B W σ p hp n (codeOutcome_mem_closure B W p n))

theorem codedSecond_winning [CompleteSpace X] (B : CodeBasis X) (W : Move X) {A : Set X}
    (σ : Strategy X) (hσ : Winning A W.openSet σ) :
    (codeTree B W).Winning (codePayoff B W A) false (codedSecondStrategy B W σ) := by
  intro p hp
  obtain ⟨x, hx, hxA⟩ := hσ _ (decodedSecond_legal B W σ p hp)
  have he := (exists_unique_outcome (decodedSecond_legal B W σ p hp)).unique
    hx (codedSecond_outcome B W σ p hp)
  change codeOutcome B W p ∉ A
  rwa [← he]


/-- The full-game move prescribed by I after the decoded II-history. -/
def firstPrescription (B : CodeBasis X) (σ : FirstStrategy X) (s : List ℕ) : Move X :=
  if s.length = 0 then σ.first
  else (σ.reply (decodedHistory B s 1 (s.length / 2 - 1)) (B.move s[s.length - 1]!)).toMove

lemma firstPrescription_prefix (B : CodeBasis X) (σ : FirstStrategy X) (p : ℕ → ℕ) (n : ℕ) :
    firstPrescription B σ (seqPrefix p (2 * n)) =
      firstMoveAt σ (fun i => B.move (p (2 * i + 1))) n := by
  cases n with
  | zero => simp [firstPrescription, firstMoveAt]
  | succ n =>
    have hh := decodedHistory_prefix B p (2 * (n + 1)) 1 n (by intro i hi; omega)
    have hlen : (seqPrefix p (2 * (n + 1))).length / 2 - 1 = n := by simp
    have hlast : (seqPrefix p (2 * (n + 1)))[(seqPrefix p (2 * (n + 1))).length - 1]! =
        p (2 * n + 1) := by
      rw [getElem!_pos (seqPrefix p (2 * (n + 1))) _ (by simp)]
      simp only [seqPrefix, List.length_ofFn, List.getElem_ofFn]
      congr 1
    rw [firstPrescription, ite_eq_right (by simp), hlen, hh, hlast]
    rfl

/-- I refines the prescribed initial move or reply; II's actual basic moves are retained. -/
def codedFirstStrategy (B : CodeBasis X) (W : Move X) (σ : FirstStrategy X)
    (hfirst : σ.first.openSet ⊆ W.openSet) : (codeTree B W).Strategy true := fun s hs => by
  have heven : s.val.length % 2 = 0 := by simpa only [TreeGames.GameTree.turn, beq_iff_eq] using hs
  let U := firstPrescription B σ s.val
  let a := B.refinement U 0
  refine ⟨a, codeLegal_append B W.openSet s.property ?_ ?_⟩
  · split_ifs with hzero
    · have hu : U = σ.first := by simp [U, firstPrescription, hzero]
      exact subset_closure.trans ((B.refinement_spec U 0).1.trans (hu ▸ hfirst))
    · apply (B.refinement_spec U 0).1.trans
      simpa only [U, firstPrescription, ite_eq_right hzero,
        getElem!_pos s.val (s.val.length - 1) (show s.val.length - 1 < s.val.length by omega)] using
        subset_closure.trans (σ.reply (decodedHistory B s.val 1 (s.val.length / 2 - 1))
          (B.move s.val[s.val.length - 1]!)).closure_subset
  · intro hodd
    omega

lemma codedFirstStrategy_refines (B : CodeBasis X) (W : Move X) (σ : FirstStrategy X)
    (hfirst : σ.first.openSet ⊆ W.openSet) (p : (codeTree B W).Play)
    (hp : (codeTree B W).Follows (codedFirstStrategy B W σ hfirst) p) (n : ℕ) :
    closure (codeMove B W p (2 * n)).openSet ⊆
      (firstMoveAt σ (fun i => codeMove B W p (2 * i + 1)) n).openSet := by
  have ht : TreeGames.GameTree.turn (seqPrefix p.val (2 * n)) = true := by
    simp [TreeGames.GameTree.turn]
  have he := hp (2 * n) ht
  change p.val (2 * n) = B.refinement (firstPrescription B σ (seqPrefix p.val (2 * n))) 0 at he
  rw [firstPrescription_prefix] at he
  change closure (B.move (p.val (2 * n))).openSet ⊆ _
  rw [he]
  exact (B.refinement_spec _ 0).1

lemma decodedFirst_legal (B : CodeBasis X) (W : Move X) (σ : FirstStrategy X)
    (hfirst : σ.first.openSet ⊆ W.openSet) (p : (codeTree B W).Play)
    (hp : (codeTree B W).Follows (codedFirstStrategy B W σ hfirst) p) :
    FirstLegal σ (fun i => codeMove B W p (2 * i + 1)) := by
  intro n
  exact ⟨(codeMove_step B W p (2 * n)).trans
    (subset_closure.trans (codedFirstStrategy_refines B W σ hfirst p hp n)),
    codeMove_bound B W p n⟩

theorem codedFirst_winning [CompleteSpace X] (B : CodeBasis X) (W : Move X) {A : Set X}
    (σ : FirstStrategy X) (hσ : FirstWinning A W.openSet σ) :
    (codeTree B W).Winning (codePayoff B W A) true (codedFirstStrategy B W σ hσ.1) := by
  intro p hp
  obtain ⟨x, hx, hxA⟩ := hσ.2 _ (decodedFirst_legal B W σ hσ.1 p hp)
  have he := (codePlay_exists_unique_outcome B W p).unique hx
    (fun n => codeOutcome_mem_closure B W p n)
  change codeOutcome B W p ∈ A
  rwa [← he]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Refining open-set strategies
-/
theorem winning_transfers_to_code [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) :
    ((∃ σ : FirstStrategy X, FirstWinning A W.openSet σ) →
      ∃ τ : (codeTree B W).Strategy true, (codeTree B W).Winning (codePayoff B W A) true τ) ∧
    ((∃ σ : Strategy X, Winning A W.openSet σ) →
      ∃ τ : (codeTree B W).Strategy false, (codeTree B W).Winning (codePayoff B W A) false τ) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨codedFirstStrategy B W σ hσ.1, codedFirst_winning B W σ hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨codedSecondStrategy B W σ, codedSecond_winning B W σ hσ⟩

end PolishSpaceBook.BanachMazurGame
