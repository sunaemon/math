module

public import PolishSpaceBook.BanachMazurGame
public import PolishSpaceBook.TreeGames
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-!
# Coding the Banach–Mazur game by natural numbers

Nonempty basic opens are the moves. Closure inclusions and the odd-round
geometric bounds define a pruned tree of legal histories. Complete metrics give
a unique outcome, and sharing a sufficiently long prefix bounds its distance.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Metric Filter Topology TopologicalSpace
open scoped Classical
variable {X : Type*} [MetricSpace X]

structure CodeBasis (X : Type*) [TopologicalSpace X] where
  move : ℕ → Move X
  isBasis : IsTopologicalBasis (range (fun n => (move n).openSet))

theorem exists_codeBasis [SecondCountableTopology X] (W : Move X) : Nonempty (CodeBasis X) := by
  obtain ⟨x, hx⟩ := W.nonempty
  obtain ⟨s, hs, _, _⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hx W.isOpen
  obtain ⟨b, hb⟩ := (countable_countableBasis X).exists_eq_range ⟨s, hs⟩
  have hm (n : ℕ) : b n ∈ countableBasis X := by rw [hb]; exact mem_range_self n
  refine ⟨⟨fun n => ⟨b n, isOpen_of_mem_countableBasis (hm n),
    nonempty_of_mem_countableBasis (hm n)⟩, ?_⟩⟩
  simpa only [hb] using isBasis_countableBasis X

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    To use games with natural-number moves, enumerate a countable basis of nonempty open sets as
    $\Sequence{B_i}{i\in\omega}$,
    allowing repetitions if the basis is finite. Every nonempty open $U$ has, for each $n$, a basic refinement satisfying
    $$\Closure{B_i}\IncludedIn U,\qquad \Diameter{B_i}\le 2^{-n}.$$
    Indeed, first choose a small open ball whose closure lies in $U$ and whose diameter is at most $2^{-n}$,
    and then choose a nonempty basic open set inside that ball.
-/
/-- Every open move has a basic refinement satisfying any prescribed round bound. -/
theorem CodeBasis.exists_small (B : CodeBasis X) (U : Move X) (n : ℕ) :
    ∃ k, closure (B.move k).openSet ⊆ U.openSet ∧
      Bornology.IsBounded (B.move k).openSet ∧ diam (B.move k).openSet ≤ (1 / 2 : ℝ) ^ n := by
  let V := smallResponse n U
  obtain ⟨x, hx⟩ := V.nonempty
  obtain ⟨s, ⟨k, rfl⟩, _, hsub⟩ := B.isBasis.exists_subset_of_mem_open hx V.isOpen
  exact ⟨k, (closure_mono hsub).trans V.closure_subset, V.bounded.subset hsub,
    (diam_mono hsub V.bounded).trans V.diam_le⟩

/-- Position zero is I's first move. Odd positions are II's diameter-constrained moves. -/
def CodeLegal (B : CodeBasis X) (W : Set X) (s : List ℕ) : Prop :=
  (∀ i (hi : i < s.length),
    if h : i = 0 then (B.move s[i]).openSet ⊆ W
    else closure (B.move s[i]).openSet ⊆ (B.move s[i - 1]).openSet) ∧
  ∀ i (hi : i < s.length), i % 2 = 1 →
    Bornology.IsBounded (B.move s[i]).openSet ∧
      diam (B.move s[i]).openSet ≤ (1 / 2 : ℝ) ^ (i / 2)

lemma codeLegal_nil (B : CodeBasis X) (W : Set X) : CodeLegal B W [] := by
  constructor <;> intro i hi <;> simp at hi

lemma codeLegal_prefix (B : CodeBasis X) (W : Set X) {s t : List ℕ}
    (ht : CodeLegal B W t) (hst : s <+: t) : CodeLegal B W s := by
  have hlen := hst.length_le
  constructor
  · intro i hi
    have hit : i < t.length := hi.trans_le hlen
    have h := ht.1 i hit
    by_cases hi0 : i = 0
    · rw [dite_eq_left hi0] at h ⊢
      rw [hst.getElem hi]
      exact h
    · have hprev : i - 1 < s.length := by omega
      rw [dite_eq_right hi0] at h ⊢
      rw [hst.getElem hi, hst.getElem hprev]
      exact h
  · intro i hi hodd
    rw [hst.getElem hi]
    exact ht.2 i (hi.trans_le hlen) hodd

lemma codeLegal_append (B : CodeBasis X) (W : Set X) {s : List ℕ} (hs : CodeLegal B W s)
    {a : ℕ}
    (hsub : if h : s.length = 0 then (B.move a).openSet ⊆ W
      else closure (B.move a).openSet ⊆ (B.move s[s.length - 1]).openSet)
    (hbound : s.length % 2 = 1 → Bornology.IsBounded (B.move a).openSet ∧
      diam (B.move a).openSet ≤ (1 / 2 : ℝ) ^ (s.length / 2)) :
    CodeLegal B W (s ++ [a]) := by
  constructor
  · intro i hi
    have hil : i ≤ s.length := by simpa using hi
    by_cases hilt : i < s.length
    · have h := hs.1 i hilt
      by_cases hi0 : i = 0
      · simpa only [dite_eq_left hi0, List.getElem_append_left hilt] using h
      · have hprev : i - 1 < s.length := by omega
        simpa only [dite_eq_right hi0, List.getElem_append_left hilt,
          List.getElem_append_left hprev] using h
    · have hie : i = s.length := by omega
      subst i
      by_cases hlen : s.length = 0
      · simpa [hlen] using hsub
      · simpa only [dite_eq_right hlen, List.getElem_concat_length rfl,
          List.getElem_append_left (show s.length - 1 < s.length by omega)] using hsub
  · intro i hi hodd
    have hil : i ≤ s.length := by simpa using hi
    by_cases hilt : i < s.length
    · simpa only [List.getElem_append_left hilt] using hs.2 i hilt hodd
    · have hie : i = s.length := by omega
      subst i
      simpa using hbound hodd

lemma codeLegal_successor (B : CodeBasis X) (W : Move X) {s : List ℕ}
    (hs : CodeLegal B W.openSet s) : ∃ a, CodeLegal B W.openSet (s ++ [a]) := by
  by_cases hlen : s.length = 0
  · obtain ⟨a, ha, hb, hd⟩ := B.exists_small W (s.length / 2)
    exact ⟨a, codeLegal_append B W.openSet hs (by simpa [hlen] using subset_closure.trans ha)
      (fun _ => ⟨hb, hd⟩)⟩
  · obtain ⟨a, ha, hb, hd⟩ := B.exists_small (B.move s[s.length - 1]) (s.length / 2)
    exact ⟨a, codeLegal_append B W.openSet hs (by simpa [hlen] using ha)
      (fun _ => ⟨hb, hd⟩)⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The empty sequence is legal, and every prefix of a legal sequence is legal because its conditions are among
    those already checked. For the first move, choose a basic open set inside $W$. After any later finite position,
    choose a basic refinement whose closure lies in the last open set. At an II-turn, also impose the current
    bound $2^{-n}$ on its diameter. The refinement construction above supplies each of these moves, so every node
    has a successor. The \termuseas{branch extension for trees without terminal nodes}{branch-extension lemma}
    makes $T$ pruned.
    By §{sec:closed-sets-trees}, its body is closed. Being closed in the Polish space $\BaireSpace$, the body is Polish.
    \end{proof}
-/
/-- The same local rules define the tree used for games on natural-number moves. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Legal code tree
-/
def codeTree (B : CodeBasis X) (W : Move X) : TreeGames.GameTree ℕ where
  nodes := {s | CodeLegal B W.openSet s}
  subtree := fun _ _ ht hst => codeLegal_prefix B W.openSet ht hst
  root_mem := codeLegal_nil B W.openSet
  successor := fun _ hs => codeLegal_successor B W hs

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Legal code tree
-/
theorem codeTree_pruned (B : CodeBasis X) (W : Move X) : IsPruned (codeTree B W).nodes :=
  (codeTree B W).isPruned


/-- Decode the open move at a given position of an infinite legal code. -/
def codeMove (B : CodeBasis X) (W : Move X) (p : (codeTree B W).Play) (i : ℕ) : Move X :=
  B.move (p.val i)

lemma codeMove_initial (B : CodeBasis X) (W : Move X) (p : (codeTree B W).Play) :
    (codeMove B W p 0).openSet ⊆ W.openSet := by
  have h := (p.property 1).1 0 (by simp [seqPrefix])
  simpa [seqPrefix, codeMove] using h

lemma codeMove_step (B : CodeBasis X) (W : Move X) (p : (codeTree B W).Play) (i : ℕ) :
    closure (codeMove B W p (i + 1)).openSet ⊆ (codeMove B W p i).openSet := by
  have h := (p.property (i + 2)).1 (i + 1) (by simp [seqPrefix])
  rw [dite_eq_right (show i + 1 ≠ 0 by omega)] at h
  simpa only [seqPrefix, List.getElem_ofFn, Nat.add_sub_cancel, codeMove] using h

lemma codeMove_bound (B : CodeBasis X) (W : Move X) (p : (codeTree B W).Play) (n : ℕ) :
    Bornology.IsBounded (codeMove B W p (2 * n + 1)).openSet ∧
      diam (codeMove B W p (2 * n + 1)).openSet ≤ (1 / 2 : ℝ) ^ n := by
  have h := (p.property (2 * n + 2)).2 (2 * n + 1) (by simp [seqPrefix]) (by omega)
  simpa only [seqPrefix, List.getElem_ofFn, codeMove, show (2 * n + 1) / 2 = n by omega] using h

lemma codeMove_closures_antitone (B : CodeBasis X) (W : Move X) (p : (codeTree B W).Play) :
    Antitone (fun n => closure (codeMove B W p (2 * n + 1)).openSet) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := (codeMove_step B W p (2 * n + 2)).trans (subset_closure.trans
    ((codeMove_step B W p (2 * n + 1)).trans subset_closure))
  convert h using 1

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Continuous outcome map
-/
theorem codePlay_exists_unique_outcome [CompleteSpace X] (B : CodeBasis X) (W : Move X)
    (p : (codeTree B W).Play) :
    ∃! x, ∀ n, x ∈ closure (codeMove B W p (2 * n + 1)).openSet :=
  exists_unique_nested_closures _ (codeMove_closures_antitone B W p)
    (fun n => (codeMove_bound B W p n).1) (fun n => (codeMove_bound B W p n).2)

def codeOutcome [CompleteSpace X] (B : CodeBasis X) (W : Move X) : (codeTree B W).Play → X :=
  fun p => (codePlay_exists_unique_outcome B W p).choose

lemma codeOutcome_mem_closure [CompleteSpace X] (B : CodeBasis X) (W : Move X)
    (p : (codeTree B W).Play) (n : ℕ) :
    codeOutcome B W p ∈ closure (codeMove B W p (2 * n + 1)).openSet :=
  (codePlay_exists_unique_outcome B W p).choose_spec.1 n

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Continuous outcome map
-/
lemma codeOutcome_mem_initial [CompleteSpace X] (B : CodeBasis X) (W : Move X)
    (p : (codeTree B W).Play) : codeOutcome B W p ∈ W.openSet :=
  codeMove_initial B W p (codeMove_step B W p 0 (codeOutcome_mem_closure B W p 0))

/-- Equal response codes put the two outcomes in one set with a known diameter bound. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Continuous outcome map
-/
lemma codeOutcome_dist_le [CompleteSpace X] (B : CodeBasis X) (W : Move X)
    (p q : (codeTree B W).Play) (n : ℕ) (h : p.val (2 * n + 1) = q.val (2 * n + 1)) :
    dist (codeOutcome B W p) (codeOutcome B W q) ≤ (1 / 2 : ℝ) ^ n := by
  have hp := codeOutcome_mem_closure B W p n
  have hq := codeOutcome_mem_closure B W q n
  have heq : codeMove B W p (2 * n + 1) = codeMove B W q (2 * n + 1) := congrArg B.move h
  rw [← heq] at hq
  exact (dist_le_diam_of_mem (codeMove_bound B W p n).1.closure hp hq).trans
    (by simpa only [Metric.diam_closure] using (codeMove_bound B W p n).2)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Decoding a branch gives a legal open-set play. The nested-closure argument above supplies its unique outcome,
    and $\pi(p)\in\Closure{B_{p(1)}}\IncludedIn B_{p(0)}\IncludedIn W$.
    If two branches agree through position $2n+1$, their outcomes lie in the closure of the same II-response.
    That closure has diameter at most $2^{-n}$, giving the displayed estimate. For any $\varepsilon>0$, choose $n$
    with $2^{-n}<\varepsilon$. The cylinder fixing the first $2n+2$ codes, intersected with $\TreeBody{T}$,
    is an open neighborhood on which outcomes lie within distance $\varepsilon$ of the given outcome.
    This proves continuity.
    \end{proof}
-/
/-- A cylinder fixing the first `2n+2` moves forces outcomes to be within `2⁻ⁿ`. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Continuous outcome map
-/
theorem continuous_codeOutcome [CompleteSpace X] (B : CodeBasis X) (W : Move X) :
    Continuous (codeOutcome B W) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hpow).2 ε hε)
  have hc : {q : (codeTree B W).Play | q.val ∈ cyl (seqPrefix p.val (2 * N + 2))} ∈ 𝓝 p :=
    ((isOpen_cyl (seqPrefix p.val (2 * N + 2))).preimage continuous_subtype_val).mem_nhds
      (mem_cyl_seqPrefix p.val (2 * N + 2))
  apply Filter.mem_of_superset hc
  intro q hq
  have heq : q.val (2 * N + 1) = p.val (2 * N + 1) := by
    have h := hq (2 * N + 1) (by simp [seqPrefix])
    simpa only [seqPrefix, List.get_eq_getElem, List.getElem_ofFn] using h
  exact (codeOutcome_dist_le B W q p N heq).trans_lt (hN N le_rfl)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Legal code tree
-/
instance codePlay_polishSpace (B : CodeBasis X) (W : Move X) :
    PolishSpace (codeTree B W).Play := (isClosed_treeBody (codeTree B W).nodes).polishSpace

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The coded payoff is exactly
    $$A_T:=\pi^{-1}(A)=\pi^{-1}(A\cap W)\IncludedIn\TreeBody{T}.$$
    Thus Borel payoffs remain Borel. More generally, any pointclass on Polish spaces closed under continuous
    preimages contains $A_T$ whenever it contains $A$. Legality is already part of the domain $\TreeBody{T}$.
    This defines the game $G(A_T,T)$ on natural-number moves.
-/
/-- The coded winner is determined by the decoded outcome, with no extra legality encoding. -/
def codePayoff [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) :
    Set (codeTree B W).Play := codeOutcome B W ⁻¹' A

lemma codePayoff_restrict [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) :
    codePayoff B W A = codeOutcome B W ⁻¹' (A ∩ W.openSet) := by
  ext p
  exact ⟨fun hp => ⟨hp, codeOutcome_mem_initial B W p⟩, And.left⟩

theorem codePayoff_borel [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X)
    (hA : @MeasurableSet X (borel X) A) :
    @MeasurableSet (codeTree B W).Play (borel (codeTree B W).Play) (codePayoff B W A) :=
  hA.preimage (continuous_codeOutcome B W).borel_measurable

/-- Package the legal code tree and decoded payoff as an integer-move game. -/
def codedGame [CompleteSpace X] (B : CodeBasis X) (W : Move X) (A : Set X) : TreeGames.Game ℕ :=
  ⟨codeTree B W, codePayoff B W A⟩

end PolishSpaceBook.BanachMazurGame
