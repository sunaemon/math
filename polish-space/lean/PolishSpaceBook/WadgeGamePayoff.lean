module

public import PolishSpaceBook.WadgeHierarchy
public import PolishSpaceBook.BorelDeterminacy
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

@[expose] public section

/-!
# The payoff of Wadge's game

A round records I's natural number and II's coded move. Zero is a pass;
`k + 1` outputs `k`. The productivity condition belongs to the winning payoff,
not to a restriction on allowed infinite plays. Removing passes is continuous
on the G-delta subspace of productive plays.
-/
noncomputable section
namespace PolishSpaceBook.WadgeGame
open Set Function Filter Topology
open scoped Classical

abbrev Play := ℕ → ℕ × ℕ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Encode a pass by $0$ and a genuine move $k$ by $k+1$. The space of round-by-round plays is
    $$P:=\seqPower{(\omega\times\omega)}{\omega},\qquad p=((a_0,c_0),(a_1,c_1),\ldots).$$
    All coordinates have the discrete topology. The plays on which II produces infinitely many genuine moves form
    $$L:=\bigcap_{N\in\omega}\bigcup_{n\ge N}\{p\in P:c_n\ne0\}.$$
    Each set in braces is a countable union of basic cylinders, hence open.
    Thus $L$ is a $\Gdelta$ subset of $P$, in particular a Borel subset.
-/
def Productive (p : Play) : Prop := ∀ N, ∃ n, N ≤ n ∧ (p n).2 ≠ 0

def genuineAfter (N : ℕ) : Set Play := ⋃ n ≥ N, {p | (p n).2 ≠ 0}

lemma genuineAfter_isOpen (N : ℕ) : IsOpen (genuineAfter N) := by
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro _
  exact (isOpen_discrete ({0}ᶜ : Set ℕ)).preimage ((continuous_apply n).snd)

lemma productive_eq_iInter : {p : Play | Productive p} = ⋂ N, genuineAfter N := by
  ext p
  simp [Productive, genuineAfter]

lemma productive_isGδ : IsGδ {p : Play | Productive p} := by
  rw [productive_eq_iInter]
  exact IsGδ.iInter_of_isOpen genuineAfter_isOpen

lemma productive_measurable : MeasurableSet {p : Play | Productive p} :=
  productive_isGδ.measurableSet

abbrev ProductivePlay := {p : Play // Productive p}

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For $p\in L$, list the positions of its genuine moves by
    $$
    \begin{aligned}
    j_0(p)&:=\min\{n:c_n\ne0\},\\
    j_{r+1}(p)&:=\min\{n>j_r(p):c_n\ne0\}.
    \end{aligned}
    $$
    The output condition makes every minimum exist. The indices increase strictly and exhaust the genuine moves,
    because each step chooses the first remaining position. Define
    $$\pi_I(p)(n):=a_n,\qquad \pi_{II}(p)(r):=c_{j_r(p)}-1.$$
    The latter subtraction is applied only to positive codes. Both maps have domain $L$ and codomain $\BaireSpace$.
    The first is a coordinate projection. For the second, if $q\in L$ agrees with $p$ through round $j_r(p)$,
    induction over the successive minima gives
    $$j_r(q)=j_r(p),\qquad \pi_{II}(q)(r)=\pi_{II}(p)(r).$$
    This fixes each output coordinate on a cylinder neighborhood relative to $L$, proving continuity.
-/
/-- First non-pass at or after `k`; the fallback is unused on productive plays. -/
def next (p : Play) (k : ℕ) : ℕ :=
  if h : ∃ n, k ≤ n ∧ (p n).2 ≠ 0 then Nat.find h else k

lemma next_spec {p : Play} (hp : Productive p) (k : ℕ) :
    k ≤ next p k ∧ (p (next p k)).2 ≠ 0 := by
  simp only [next, dite_eq_left (hp k)]
  exact Nat.find_spec (hp k)

lemma next_le {p : Play} (hp : Productive p) {k n : ℕ}
    (hkn : k ≤ n) (hn : (p n).2 ≠ 0) : next p k ≤ n := by
  simp only [next, dite_eq_left (hp k)]
  exact Nat.find_min' (hp k) ⟨hkn, hn⟩

lemma next_congr {p q : Play} (hp : Productive p) (hq : Productive q) (k : ℕ)
    (h : ∀ i ≤ next p k, (p i).2 = (q i).2) : next p k = next q k := by
  have hp' := next_spec hp k
  have hqle : next q k ≤ next p k := next_le hq hp'.1 (by rw [← h _ le_rfl]; exact hp'.2)
  have hq' := next_spec hq k
  apply le_antisymm _ hqle
  apply next_le hp hq'.1
  rw [h _ hqle]
  exact hq'.2

/-- The positions of the successive genuine moves. -/
def genuineIndex (p : Play) : ℕ → ℕ
  | 0 => next p 0
  | n + 1 => next p (genuineIndex p n + 1)

lemma genuineIndex_nonzero {p : Play} (hp : Productive p) (n : ℕ) :
    (p (genuineIndex p n)).2 ≠ 0 := by
  cases n
  · exact (next_spec hp 0).2
  · exact (next_spec hp _).2

lemma genuineIndex_strictMono {p : Play} (hp : Productive p) : StrictMono (genuineIndex p) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact Nat.lt_of_succ_le (next_spec hp _).1

/-- The successive least positions exhaust all genuine moves. -/
lemma genuineIndex_exhaustive {p : Play} (hp : Productive p) {i : ℕ} (hi : (p i).2 ≠ 0) :
    ∃ n, genuineIndex p n = i := by
  have hex : ∃ n, i ≤ genuineIndex p n := ⟨i, (genuineIndex_strictMono hp).id_le i⟩
  let n := Nat.find hex
  have hn : i ≤ genuineIndex p n := Nat.find_spec hex
  refine ⟨n, le_antisymm ?_ hn⟩
  cases he : n with
  | zero => exact next_le hp (Nat.zero_le i) hi
  | succ m =>
    have hm : ¬ i ≤ genuineIndex p m := Nat.find_min hex (by change m < n; omega)
    exact next_le hp (by omega) hi

lemma genuineIndex_congr {p q : Play} (hp : Productive p) (hq : Productive q) (n : ℕ)
    (h : ∀ i ≤ genuineIndex p n, (p i).2 = (q i).2) : genuineIndex p n = genuineIndex q n := by
  induction n with
  | zero => exact next_congr hp hq 0 h
  | succ n ih =>
    have hn : genuineIndex p n ≤ genuineIndex p (n + 1) :=
      (genuineIndex_strictMono hp).monotone (Nat.le_succ n)
    have he := ih (fun i hi => h i (hi.trans hn))
    simp only [genuineIndex, ← he]
    exact next_congr hp hq _ h

/-- I's output is read without deleting any coordinates. -/
def firstOutput (p : Play) : ℕ → ℕ := fun n => (p n).1
/-- II's genuine code is positive, so this subtraction decodes `k + 1` as `k`. -/
def secondOutput (p : ProductivePlay) : ℕ → ℕ := fun n => (p.val (genuineIndex p.val n)).2 - 1

lemma firstOutput_continuous : Continuous firstOutput :=
  continuous_pi (fun n => (continuous_apply n).fst)

lemma secondOutput_coordinate_eq {p q : ProductivePlay} {n : ℕ}
    (h : ∀ i ≤ genuineIndex p.val n, (p.val i).2 = (q.val i).2) :
    secondOutput p n = secondOutput q n := by
  have he := genuineIndex_congr p.property q.property n h
  dsimp only [secondOutput]
  rw [← he, h _ le_rfl]

lemma secondOutput_continuous : Continuous secondOutput := by
  apply continuous_pi
  intro n
  rw [continuous_iff_continuousAt]
  intro p
  apply Filter.EventuallyEq.continuousAt (y := secondOutput p n)
  filter_upwards [((isOpen_cyl (seqPrefix p.val (genuineIndex p.val n + 1))).preimage
    continuous_subtype_val).mem_nhds (mem_cyl_seqPrefix p.val _)] with q hq
  apply secondOutput_coordinate_eq (p := q) (q := p)
  have hprefix : ∀ i ≤ genuineIndex p.val n, (p.val i).2 = (q.val i).2 := by
    intro i hi
    exact (congrArg Prod.snd ((hq i (by simp; omega)).trans (seqPrefix_get p.val _))).symm
  have he := genuineIndex_congr p.property q.property n hprefix
  intro i hi
  exact (hprefix i (by omega)).symm

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Inside $L$, the matching-membership condition is the set
    $$
    E:=\bigl(\pi_I^{-1}(A)\cap\pi_{II}^{-1}(B)\bigr)
    \cup
    \bigl(\pi_I^{-1}(\SetDifference{\BaireSpace}{A})\cap
    \pi_{II}^{-1}(\SetDifference{\BaireSpace}{B})\bigr).
    $$
    It is Borel in $L$ by continuity. Let $\iota:L\hookrightarrow P$ be inclusion. The actual payoff for II in the
    whole play space is $W_{II}:=\iota[E]$. Since $L$ is Borel in $P$, every relatively Borel subset of $L$ is Borel
    in $P$, so $W_{II}$ is Borel. Its complement $\SetDifference{P}{W_{II}}$ is I's payoff and is Borel as well.
    In particular, every play outside $L$ is a loss for II.
-/
/-- Match the two memberships on the productive subspace. -/
def matchingPayoff (A B : Set (ℕ → ℕ)) : Set ProductivePlay :=
  {p | firstOutput p.val ∈ A ↔ secondOutput p ∈ B}

lemma matchingPayoff_measurable {A B : Set (ℕ → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (matchingPayoff A B) := by
  have hI : MeasurableSet ((fun p : ProductivePlay => firstOutput p.val) ⁻¹' A) := hA.preimage (firstOutput_continuous.comp continuous_subtype_val).measurable
  have hII := hB.preimage secondOutput_continuous.measurable
  have he : matchingPayoff A B =
      ((fun p : ProductivePlay => firstOutput p.val) ⁻¹' A ∩ secondOutput ⁻¹' B) ∪
      ((fun p : ProductivePlay => firstOutput p.val) ⁻¹' Aᶜ ∩ secondOutput ⁻¹' Bᶜ) := by
    ext p
    simp only [matchingPayoff, mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff]
    tauto
  rw [he]
  exact (hI.inter hII).union (hI.compl.inter hII.compl)

/-- All nonproductive plays are outside II's payoff. -/
def secondPayoff (A B : Set (ℕ → ℕ)) : Set Play := Subtype.val '' matchingPayoff A B

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: lemma
  title: Borelness of Wadge payoffs
-/
theorem secondPayoff_measurable {A B : Set (ℕ → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (secondPayoff A B) :=
  productive_measurable.subtype_image (matchingPayoff_measurable hA hB)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: lemma
  title: Borelness of Wadge payoffs
-/
lemma not_mem_secondPayoff_of_not_productive {A B : Set (ℕ → ℕ)} {p : Play}
    (hp : ¬ Productive p) : p ∉ secondPayoff A B := by
  rintro ⟨q, _, rfl⟩
  exact hp q.property

lemma mem_secondPayoff {A B : Set (ℕ → ℕ)} (p : ProductivePlay) :
    p.val ∈ secondPayoff A B ↔ (firstOutput p.val ∈ A ↔ secondOutput p ∈ B) := by
  constructor
  · rintro ⟨q, hq, he⟩
    have hqp : q = p := Subtype.ext he
    simpa only [hqp, matchingPayoff, mem_ofPred_eq] using hq
  · intro h
    exact ⟨p, h, rfl⟩

/-- The complementary payoff makes every nonproductive play a win for I. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: lemma
  title: Borelness of Wadge payoffs
-/
theorem firstPayoff_measurable {A B : Set (ℕ → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (secondPayoff A B)ᶜ := (secondPayoff_measurable hA hB).compl


/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Finally, pass to the alternating integer presentation. The map
    $$\rho:\BaireSpace\to P,\qquad \rho(z)(n):=(z(2n),z(2n+1))$$
    is continuous and bijective; its inverse interleaves the two coordinates of each round.
    I's integer payoff is $\rho^{-1}(\SetDifference{P}{W_{II}})$, which is Borel by continuity.
    This is the ordinary integer game to which Borel determinacy applies.
    \end{proof}
-/
/-- Even and odd integer moves form one round of the game. -/
def roundPlay (a : ℕ → ℕ) : Play := fun n => (a (2 * n), a (2 * n + 1))

lemma roundPlay_continuous : Continuous roundPlay :=
  continuous_pi (fun n => (continuous_apply (2 * n)).prodMk (continuous_apply (2 * n + 1)))

/-- Every round stream has the corresponding alternating integer presentation. -/
def interleave (p : Play) (i : ℕ) : ℕ :=
  if i % 2 = 0 then (p (i / 2)).1 else (p (i / 2)).2

lemma roundPlay_interleave (p : Play) : roundPlay (interleave p) = p := by
  funext n
  simp [roundPlay, interleave, Nat.add_div]

lemma interleave_roundPlay (a : ℕ → ℕ) : interleave (roundPlay a) = a := by
  funext i
  simp only [interleave, roundPlay]
  split_ifs with h
  · congr 1; omega
  · congr 1; omega

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Wadge degrees are computed by games. For $A, B \IncludedIn \BaireSpace$, the \termdefine{Wadge game} $G_W(A, B)$ is
    played as follows. At round $n$, Player I plays a natural number $a_n$, and Player II replies with a natural number
    or a *pass*. Every finite sequence of such moves is allowed. II must make infinitely many non-pass moves to win:
    II may wait any finite number of rounds for the next output coordinate, but must eventually produce every coordinate.
    A play satisfying this output condition produces
    $$x \;:=\; (a_0, a_1, \ldots) \in \BaireSpace, \qquad y \;:=\; (\text{II's genuine moves in order}) \in \BaireSpace.$$
    *II wins* iff
    $$x \in A \;\Longleftrightarrow\; y \in B.$$
    The pass option is the technical mechanism that lets II observe enough of $x$ before committing to coordinates of $y$.
    Plays with only finitely many genuine moves are losses for II.
-/
/-- Player I wins the complement of II's payoff, including all nonproductive plays. -/
def integerPayoff (A B : Set (ℕ → ℕ)) : Set (ℕ → ℕ) := roundPlay ⁻¹' (secondPayoff A B)ᶜ

abbrev FirstStrategy := BaireIStrategy
abbrev SecondStrategy := BaireIIStrategy
def FirstWinning (A B : Set (ℕ → ℕ)) (σ : FirstStrategy) : Prop := BaireIWinning (integerPayoff A B) σ
def SecondWinning (A B : Set (ℕ → ℕ)) (τ : SecondStrategy) : Prop := BaireIIWinning (integerPayoff A B) τ
def Determined (A B : Set (ℕ → ℕ)) : Prop := BaireDetermined (integerPayoff A B)

lemma integerPayoff_measurable {A B : Set (ℕ → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (integerPayoff A B) :=
  (firstPayoff_measurable hA hB).preimage roundPlay_continuous.measurable

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Hence Borel determinacy from §{sec:martin-borel-det} supplies the determinacy hypothesis in ZFC. For arbitrary subsets
    of $\BaireSpace$, the same conclusion holds under AD.
-/
/-- Apply the imported and transported Borel-determinacy theorem to the actual integer payoff. -/
theorem determined_of_borel_determinacy
    {A B : Set (ℕ → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) : Determined A B :=
  baire_borel_determined (integerPayoff_measurable hA hB)

/-- The same integer coding applies without regularity assumptions under AD. -/
theorem determined_of_all_integer_games
    (hdet : ∀ C : Set (ℕ → ℕ), BaireDetermined C) (A B : Set (ℕ → ℕ)) : Determined A B :=
  hdet (integerPayoff A B)

end PolishSpaceBook.WadgeGame
