module

public import PolishSpaceBook.HarringtonCoveringGame
public import PolishSpaceBook.TreeGames

@[expose] public section

/-!
# Coding the covering game

The measure budget is a condition on legal finite histories. The target map is
continuous; being caught by a response is open, so avoiding every response is
closed. These facts account for the pointclass of the coded payoff. The external
exclusion of first-player winning strategies is kept as an explicit hypothesis.
-/
noncomputable section
namespace PolishSpaceBook.HarringtonCoveringGame
open Set Function Filter Topology TopologicalSpace MeasureTheory TreeGames.GameTree
open scoped Classical ENNReal

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    To make the payoff complexity explicit, let $\mathcal C$ be the clopen subsets of $\CantorSpace$.
    This family is countable: every clopen set is compact and is therefore a finite union of basic cylinders.
    Fix an injection $c:\mathcal C\to\omega$ and put $C:=c[\mathcal C]$.
    Write $D_k:=c^{-1}(k)$ for $k\in C$, and put $D_k:=\emptyset$ otherwise.
    Let $T_{\mu,\varepsilon}\IncludedIn\finseq{\omega}$ consist of the finite histories satisfying
    $$
    \begin{aligned}
    s(2n)&\in2 &&\text{if }2n<|s|,\\
    s(2n+1)&\in C,\quad
    \mu(D_{s(2n+1)})\le\varepsilon 2^{-2n-2}
    &&\text{if }2n+1<|s|.
    \end{aligned}
    $$
    These conditions are preserved by taking initial segments. Every legal history can be extended:
    I can play $0$, and II can play $c(\emptyset)$. Thus $T_{\mu,\varepsilon}$ is pruned, and its branch space
    $P:=\TreeBody{T_{\mu,\varepsilon}}$ is a closed subspace of $\BaireSpace$, hence Polish.
    For a branch $a\in P$, recover I's target and II's responses by
    $$\pi(a)(n):=a(2n),\qquad R_n(a):=D_{a(2n+1)}.$$
-/
instance clopensEncodable : Encodable (Clopens Cantor) := Encodable.ofCountable _
abbrev clopenCode (G : Clopens Cantor) : ℕ := Encodable.encode G
def decodeClopen (k : ℕ) : Clopens Cantor := (Encodable.decode (α := Clopens Cantor) k).getD ⊥
abbrev bitCode (b : Bool) : ℕ := b.toNat
def decodeBit (k : ℕ) : Bool := k == 1

@[simp] lemma decodeClopen_code (G : Clopens Cantor) : decodeClopen (clopenCode G) = G := by
  simp [decodeClopen, clopenCode]
@[simp] lemma decodeBit_code (b : Bool) : decodeBit (bitCode b) = b := by cases b <;> rfl
lemma code_decodeClopen {k : ℕ} (h : k ∈ range clopenCode) : clopenCode (decodeClopen k) = k := by
  obtain ⟨G, rfl⟩ := h
  simp

/-- The first player chooses a bit; the second chooses a clopen within the round's budget. -/
def MoveLegal (μ : Measure Cantor) (ε : ℝ≥0∞) (i k : ℕ) : Prop :=
  if i % 2 = 0 then k ≤ 1 else
    k ∈ range clopenCode ∧ μ (decodeClopen k) ≤ ε * (2⁻¹ : ℝ≥0∞) ^ (2 * (i / 2) + 2)
def CodeLegal (μ : Measure Cantor) (ε : ℝ≥0∞) (s : List ℕ) : Prop :=
  ∀ i (hi : i < s.length), MoveLegal μ ε i s[i]

lemma codeLegal_nil (μ : Measure Cantor) (ε : ℝ≥0∞) : CodeLegal μ ε [] := by
  intro i hi
  simp at hi
lemma codeLegal_prefix {μ : Measure Cantor} {ε : ℝ≥0∞} {s t : List ℕ}
    (ht : CodeLegal μ ε t) (hst : s <+: t) : CodeLegal μ ε s := by
  intro i hi
  rw [hst.getElem hi]
  exact ht i (hi.trans_le hst.length_le)
lemma codeLegal_append {μ : Measure Cantor} {ε : ℝ≥0∞} {s : List ℕ}
    (hs : CodeLegal μ ε s) {k : ℕ} (hk : MoveLegal μ ε s.length k) : CodeLegal μ ε (s ++ [k]) := by
  intro i hi
  by_cases his : i < s.length
  · simpa only [List.getElem_append_left his] using hs i his
  · have hie : i = s.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hk

/-- Empty clopens keep the legal tree pruned even when a budget is zero. -/
def codeTree (μ : Measure Cantor) (ε : ℝ≥0∞) : TreeGames.GameTree ℕ where
  nodes := {s | CodeLegal μ ε s}
  subtree := fun _ _ ht hst => codeLegal_prefix ht hst
  root_mem := codeLegal_nil μ ε
  successor := by
    intro s hs
    by_cases he : s.length % 2 = 0
    · exact ⟨0, codeLegal_append hs (by simp [MoveLegal, he])⟩
    · refine ⟨clopenCode ⊥, codeLegal_append hs ?_⟩
      rw [MoveLegal, ite_eq_right he]
      exact ⟨mem_range_self _, by simp⟩

theorem codeTree_pruned (μ : Measure Cantor) (ε : ℝ≥0∞) : IsPruned (codeTree μ ε).nodes :=
  (codeTree μ ε).isPruned
instance cantor_polish : PolishSpace Cantor := by
  let : ∀ _ : ℕ, PolishSpace Bool := fun _ => inferInstance
  exact countable_product_polish
instance codePlay_polish (μ : Measure Cantor) (ε : ℝ≥0∞) : PolishSpace (codeTree μ ε).Play :=
  (isClosed_treeBody (codeTree μ ε).nodes).polishSpace

variable {μ : Measure Cantor} {ε : ℝ≥0∞}

lemma play_move_legal (p : (codeTree μ ε).Play) (i : ℕ) : MoveLegal μ ε i (p.val i) := by
  have h := p.property (i + 1) i (by simp)
  simpa only [seqPrefix, List.getElem_ofFn] using h

/-- Read I's target, independently of II's clopen responses. -/
def target (p : (codeTree μ ε).Play) : Cantor := fun n => decodeBit (p.val (2 * n))
def response (p : (codeTree μ ε).Play) (n : ℕ) : Clopens Cantor := decodeClopen (p.val (2 * n + 1))

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-game payoff coding
-/
lemma target_continuous : Continuous (target (μ := μ) (ε := ε)) := by
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology : Continuous decodeBit).comp
    ((continuous_apply (2 * n)).comp continuous_subtype_val)

/-- The event that the response at round `n` catches the target. -/
def hitSet (n : ℕ) : Set (codeTree μ ε).Play := {p | target p ∈ response p n}
def avoidSet : Set (codeTree μ ε).Play := ⋂ n, (hitSet n)ᶜ
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-game payoff coding
-/
def codePayoff (B : Set Cantor) : Set (codeTree μ ε).Play := target ⁻¹' B ∩ avoidSet

lemma hitSet_eq_iUnion (n : ℕ) : hitSet (μ := μ) (ε := ε) n =
    ⋃ k : ℕ, {p | p.val (2 * n + 1) = k} ∩ target ⁻¹' (decodeClopen k : Set Cantor) := by
  ext p
  simp only [hitSet, response, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨_, rfl, h⟩
  · rintro ⟨k, hk, h⟩
    change target p ∈ (decodeClopen (p.val (2 * n + 1)) : Set Cantor)
    rw [hk]
    exact h

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-game payoff coding
-/
lemma hitSet_isOpen (n : ℕ) : IsOpen (hitSet (μ := μ) (ε := ε) n) := by
  rw [hitSet_eq_iUnion]
  apply isOpen_iUnion
  intro k
  have hp : Continuous (fun p : (codeTree μ ε).Play => p.val (2 * n + 1)) :=
    (continuous_apply (2 * n + 1)).comp continuous_subtype_val
  have hc : IsOpen {p : (codeTree μ ε).Play | p.val (2 * n + 1) = k} :=
    (isOpen_discrete ({k} : Set ℕ)).preimage hp
  exact hc.inter ((decodeClopen k).isOpen.preimage target_continuous)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-game payoff coding
-/
lemma avoidSet_isClosed : IsClosed (avoidSet (μ := μ) (ε := ε)) :=
  isClosed_iInter (fun n => (hitSet_isOpen n).isClosed_compl)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Each coordinate of $\pi$ is an even coordinate of $a$, so $\pi$ is continuous. Moreover,
    $$E_n=\bigcup_{k\in\omega}\bigl(\{a\in P:a(2n+1)=k\}\cap\pi^{-1}(D_k)\bigr).$$
    The coordinate condition defines an open cylinder, and $D_k$ is open. Every term in the union is therefore
    open. Taking complements and intersections proves that $F$ is closed. Membership in $F$ means that the target
    avoids every response, which gives the payoff formula. The stated closure properties give the last assertion.
    \end{proof}
-/
/-- The closure assumptions used below suffice for the actual coded payoff. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-game payoff coding
-/
theorem codePayoff_in_pointclass
    (Γ : (Y : Type) → TopologicalSpace Y → Set Y → Prop)
    (hpull : ∀ {Y Z : Type} [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]
      [PolishSpace Y] [PolishSpace Z] {f : Y → Z} {B : Set Z},
      Continuous f → Γ Z tZ B → Γ Y tY (f ⁻¹' B))
    (hclosed : ∀ {Y : Type} [tY : TopologicalSpace Y] [PolishSpace Y] {D : Set Y},
      IsClosed D → Γ Y tY D)
    (hinter : ∀ {Y : Type} [tY : TopologicalSpace Y] [PolishSpace Y] {B D : Set Y},
      Γ Y tY B → Γ Y tY D → Γ Y tY (B ∩ D))
    {B : Set Cantor} (hB : Γ Cantor inferInstance B) :
    Γ (codeTree μ ε).Play inferInstance (codePayoff B) :=
  hinter (hpull target_continuous hB) (hclosed avoidSet_isClosed)


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Let $\widehat\tau$ be the coded strategy. Retain the complete simulated code history, starting with
    $q_0:=\emptySeq$. After I plays the current bit $x(n)$, set
    $$
    \begin{aligned}
    k_n&:=\widehat\tau(q_n\concat(x(n))),& G_n&:=D_{k_n},\\
    q_{n+1}&:=q_n\concat(x(n),k_n).
    \end{aligned}
    $$
    Inductively, $q_n$ is legal and has length $2n$. Appending I's bit is legal, and the strategy returns a legal
    code $k_n\in C$ with $\mu(G_n)\le\varepsilon 2^{-2n-2}$. Thus the recurrence defines a budgeted strategy of II;
    its response depends only on the bits played so far, since these determine the earlier simulated history.
    For every $x$, the resulting code play follows $\widehat\tau$, and its target is $x$. If $x\in B$ avoided
    every $G_n$, that play would belong to $B_{\mu,\varepsilon}$, contradicting that $\widehat\tau$ wins for II.
    Thus every $x\in B$ is caught, as required.
    \end{proof}
-/
/-- Read II's prescribed code, with an unused fallback off legal odd histories. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting a covering strategy
-/
def answerCode (τ : (codeTree μ ε).Strategy false) (h : List ℕ) : ℕ :=
  if hh : CodeLegal μ ε h ∧ turn h = false then (τ ⟨h, hh.1⟩ hh.2).val else clopenCode ⊥

lemma answerCode_position (τ : (codeTree μ ε).Strategy false)
    (q : (codeTree μ ε).Position) (ht : turn q.val = false) : answerCode τ q.val = (τ q ht).val := by
  simp only [answerCode, dite_eq_left (show CodeLegal μ ε q.val ∧ turn q.val = false from ⟨q.property, ht⟩)]

lemma answerCode_legal (τ : (codeTree μ ε).Strategy false) {h : List ℕ}
    (hh : CodeLegal μ ε h) (ht : turn h = false) : CodeLegal μ ε (h ++ [answerCode τ h]) := by
  have he := answerCode_position τ ⟨h, hh⟩ ht
  change answerCode τ h = _ at he
  rw [he]
  exact (τ ⟨h, hh⟩ ht).property

lemma answerCode_move (τ : (codeTree μ ε).Strategy false) {h : List ℕ}
    (hh : CodeLegal μ ε h) (ht : turn h = false) : MoveLegal μ ε h.length (answerCode τ h) := by
  have ha := answerCode_legal τ hh ht h.length (by simp)
  simpa using ha

/-- The complete simulated history after I has supplied finitely many bits. -/
def codeHistory (τ : (codeTree μ ε).Strategy false) (b : List Bool) : List ℕ :=
  b.foldl (fun h v => h ++ [bitCode v, answerCode τ (h ++ [bitCode v])]) []

lemma codeHistory_append (τ : (codeTree μ ε).Strategy false) (b : List Bool) (v : Bool) :
    codeHistory τ (b ++ [v]) = codeHistory τ b ++
      [bitCode v, answerCode τ (codeHistory τ b ++ [bitCode v])] := by
  simp [codeHistory, List.foldl_append]

lemma codeHistory_spec (τ : (codeTree μ ε).Strategy false) (b : List Bool) :
    CodeLegal μ ε (codeHistory τ b) ∧ (codeHistory τ b).length = 2 * b.length := by
  induction b using List.reverseRecOn with
  | nil => exact ⟨codeLegal_nil μ ε, rfl⟩
  | append_singleton b v ih =>
    have hv : MoveLegal μ ε (codeHistory τ b).length (bitCode v) := by
      rw [MoveLegal, ih.2, ite_eq_left (by omega)]
      cases v <;> decide
    have hh := codeLegal_append ih.1 hv
    have ht : turn (codeHistory τ b ++ [bitCode v]) = false := by simp [turn, ih.2]
    rw [codeHistory_append]
    constructor
    · simpa only [List.append_assoc, List.singleton_append] using answerCode_legal τ hh ht
    · simp [ih.2]; omega

/-- The next clopen response after the past bits and the current bit. -/
def responseOf (τ : (codeTree μ ε).Strategy false) (b : List Bool) (v : Bool) : Clopens Cantor :=
  decodeClopen (answerCode τ (codeHistory τ b ++ [bitCode v]))

lemma responseOf_spec (τ : (codeTree μ ε).Strategy false) (b : List Bool) (v : Bool) :
    answerCode τ (codeHistory τ b ++ [bitCode v]) ∈ range clopenCode ∧
      μ (responseOf τ b v) ≤ ε * (2⁻¹ : ℝ≥0∞) ^ (2 * b.length + 2) := by
  have hs := codeHistory_spec τ b
  have hv : MoveLegal μ ε (codeHistory τ b).length (bitCode v) := by
    rw [MoveLegal, hs.2, ite_eq_left (by omega)]
    cases v <;> decide
  have hh := codeLegal_append hs.1 hv
  have ht : turn (codeHistory τ b ++ [bitCode v]) = false := by simp [turn, hs.2]
  have hm := answerCode_move τ hh ht
  simpa [MoveLegal, responseOf, hs.2, Nat.add_div] using hm

lemma responseOf_code (τ : (codeTree μ ε).Strategy false) (b : List Bool) (v : Bool) :
    clopenCode (responseOf τ b v) = answerCode τ (codeHistory τ b ++ [bitCode v]) :=
  code_decodeClopen (responseOf_spec τ b v).1

/-- Supply the budgeted strategy required by the covering estimate. -/
def liftStrategy (τ : (codeTree μ ε).Strategy false) : Strategy μ ε where
  response n h := responseOf τ (List.ofFn (fun i : Fin n => h i.castSucc)) (h (Fin.last n))
  budget := by
    intro n h
    simpa using (responseOf_spec τ (List.ofFn (fun i : Fin n => h i.castSucc)) (h (Fin.last n))).2

lemma liftStrategy_response (τ : (codeTree μ ε).Strategy false) (x : Cantor) (n : ℕ) :
    (liftStrategy τ).response n (fun i => x i) = responseOf τ (seqPrefix x n) (x n) := rfl

/-- Canonically code a legal play of bits and budgeted clopens. -/
def playWord (x : Cantor) (G : ℕ → Clopens Cantor) (i : ℕ) : ℕ :=
  if i % 2 = 0 then bitCode (x (i / 2)) else clopenCode (G (i / 2))

@[simp] lemma playWord_even (x : Cantor) (G : ℕ → Clopens Cantor) (n : ℕ) :
    playWord x G (2 * n) = bitCode (x n) := by simp [playWord]
@[simp] lemma playWord_odd (x : Cantor) (G : ℕ → Clopens Cantor) (n : ℕ) :
    playWord x G (2 * n + 1) = clopenCode (G n) := by simp [playWord, Nat.add_div]

lemma playWord_legal (x : Cantor) (G : ℕ → Clopens Cantor)
    (hG : ∀ n, μ (G n) ≤ ε * (2⁻¹ : ℝ≥0∞) ^ (2 * n + 2)) (n : ℕ) :
    CodeLegal μ ε (seqPrefix (playWord x G) n) := by
  intro i hi
  simp only [seqPrefix, List.getElem_ofFn, MoveLegal, playWord]
  split_ifs
  · cases x (i / 2) <;> decide
  · exact ⟨mem_range_self _, by simpa using hG (i / 2)⟩

def codePlay (x : Cantor) (G : ℕ → Clopens Cantor)
    (hG : ∀ n, μ (G n) ≤ ε * (2⁻¹ : ℝ≥0∞) ^ (2 * n + 2)) : (codeTree μ ε).Play :=
  ⟨playWord x G, playWord_legal x G hG⟩

@[simp] lemma target_codePlay (x : Cantor) (G : ℕ → Clopens Cantor) (hG) :
    target (codePlay (μ := μ) (ε := ε) x G hG) = x := by
  funext n
  simp [target, codePlay]
@[simp] lemma response_codePlay (x : Cantor) (G : ℕ → Clopens Cantor) (hG) (n : ℕ) :
    response (codePlay (μ := μ) (ε := ε) x G hG) n = G n := by simp [response, codePlay]

lemma playWord_prefix_succ (x : Cantor) (G : ℕ → Clopens Cantor) (n : ℕ) :
    seqPrefix (playWord x G) (2 * (n + 1)) =
      seqPrefix (playWord x G) (2 * n) ++ [bitCode (x n), clopenCode (G n)] := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    seqPrefix_succ_eq_concat, seqPrefix_succ_eq_concat]
  simp [List.append_assoc]

lemma liftStrategy_prefix (τ : (codeTree μ ε).Strategy false) (x : Cantor) (n : ℕ) :
    seqPrefix (playWord x (fun k => (liftStrategy τ).response k (fun i => x i))) (2 * n) =
      codeHistory τ (seqPrefix x n) := by
  induction n with
  | zero => simp [seqPrefix, codeHistory]
  | succ n ih =>
    rw [playWord_prefix_succ, ih, seqPrefix_succ_eq_concat, codeHistory_append]
    simp only [liftStrategy_response, responseOf_code]

lemma liftStrategy_follows (τ : (codeTree μ ε).Strategy false) (x : Cantor) :
    (codeTree μ ε).Follows τ (codePlay x
      (fun n => (liftStrategy τ).response n (fun i => x i))
      (fun n => (liftStrategy τ).budget n (fun i => x i))) := by
  intro n ht
  have he : n % 2 ≠ 0 := by simpa [turn] using ht
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  let G := fun n => (liftStrategy τ).response n (fun i => x i)
  let p := codePlay x G (fun n => (liftStrategy τ).budget n (fun i => x i))
  have hh : ((codeTree μ ε).prefixPosition p (2 * k + 1)).val =
      codeHistory τ (seqPrefix x k) ++ [bitCode (x k)] := by
    change seqPrefix (playWord x G) (2 * k + 1) = _
    rw [seqPrefix_succ_eq_concat, liftStrategy_prefix, playWord_even]
  calc
    p.val (2 * k + 1) = clopenCode (responseOf τ (seqPrefix x k) (x k)) := by
      simp [p, codePlay, G, liftStrategy_response]
    _ = answerCode τ (codeHistory τ (seqPrefix x k) ++ [bitCode (x k)]) := responseOf_code τ _ _
    _ = (τ ((codeTree μ ε).prefixPosition p (2 * k + 1)) ht).val := by
      rw [← hh]
      exact answerCode_position τ _ ht

/-- A coded win for II supplies the strategy used in the small-cover lemma. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Lifting a covering strategy
-/
theorem liftStrategy_winning {B : Set Cantor} {τ : (codeTree μ ε).Strategy false}
    (hτ : (codeTree μ ε).Winning (codePayoff B) false τ) : Winning (liftStrategy τ) B := by
  intro x hx
  by_contra! hn
  let G := fun n => (liftStrategy τ).response n (fun i => x i)
  let p := codePlay x G (fun n => (liftStrategy τ).budget n (fun i => x i))
  have hw := hτ p (liftStrategy_follows τ x)
  apply hw
  refine ⟨?_, ?_⟩
  · simpa [p] using hx
  · apply mem_iInter.mpr
    intro n
    change target p ∉ response p n
    simpa [p, G] using hn n


/-- Determinacy together with the external exclusion of I supplies a budgeted cover. -/
theorem winning_of_determined {B : Set Cantor}
    (hdet : (codeTree μ ε).Determined (codePayoff B))
    (hnoI : ¬ ∃ σ : (codeTree μ ε).Strategy true,
      (codeTree μ ε).Winning (codePayoff B) true σ) :
    ∃ σ : Strategy μ ε, Winning σ B := by
  rcases hdet with hI | ⟨τ, hτ⟩
  · exact (hnoI hI).elim
  · exact ⟨liftStrategy τ, liftStrategy_winning hτ⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    This form follows using the external game lemma above; the general determinacy-to-measurability theorem is due to
    Mycielski and Świerczkowski [@MycielskiSwierczkowski1964; @Moschovakis2009, 6A.18].

    \begin{proof}[Proof using the game lemma]
    Let $H\supseteq A$ be Borel and suppose that $B:=\SetDifference{H}{A}$ contains no Borel subset of positive
    measure. Closure under finite Boolean operations gives $B\in\Gamma$. For every $\varepsilon>0$, the payoff
    formula gives $B_{\mu,\varepsilon}=\pi^{-1}(B)\cap F\in\Gamma$, since $F$ is closed. The coded game is therefore
    determined. The external game lemma rules out a winning strategy for I, so II has a winning coded strategy.
    Lifting it gives a winning covering strategy on $B$ with budget $\varepsilon$. This works for every positive
    budget and every such $H$. The Borel hull criterion now gives the asserted measurability.
    \end{proof}
-/
/-- The local reduction is conditional on the cited covering-game lemma, recorded
as `hnoI`; no proof of that external result is asserted here. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Mycielski--Świerczkowski
-/
theorem pointclass_determinacy_measurable
    (Γ : (Y : Type) → TopologicalSpace Y → Set Y → Prop)
    (hpull : ∀ {Y Z : Type} [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]
      [PolishSpace Y] [PolishSpace Z] {f : Y → Z} {B : Set Z},
      Continuous f → Γ Z tZ B → Γ Y tY (f ⁻¹' B))
    (hborel : ∀ {Y : Type} [tY : TopologicalSpace Y] [PolishSpace Y]
      [MeasurableSpace Y] [BorelSpace Y] {D : Set Y}, MeasurableSet D → Γ Y tY D)
    (hinter : ∀ {Y : Type} [tY : TopologicalSpace Y] [PolishSpace Y] {B D : Set Y},
      Γ Y tY B → Γ Y tY D → Γ Y tY (B ∩ D))
    (hdiff : ∀ {Y : Type} [tY : TopologicalSpace Y] [PolishSpace Y] {B D : Set Y},
      Γ Y tY B → Γ Y tY D → Γ Y tY (B \ D))
    (hdet : ∀ (T : TreeGames.GameTree ℕ) (B : Set T.Play),
      Γ T.Play inferInstance B → T.Determined B)
    (μ : Measure Cantor) [IsFiniteMeasure μ]
    (hnoI : ∀ B : Set Cantor,
      (∀ C : Set Cantor, MeasurableSet C → C ⊆ B → μ C = 0) →
      ∀ ε : ℝ≥0∞, 0 < ε → ε < ∞ →
        ¬ ∃ σ : (codeTree μ ε).Strategy true,
          (codeTree μ ε).Winning (codePayoff B) true σ)
    {A : Set Cantor} (hA : Γ Cantor inferInstance A) : NullMeasurableSet A μ := by
  apply nullMeasurable_of_defect_strategies μ A
  intro H hH _ hzero ε hε hεfin
  have hB := hdiff (hborel hH) hA
  have hclosed : ∀ {Y : Type} [tY : TopologicalSpace Y] [PolishSpace Y] {D : Set Y},
      IsClosed D → Γ Y tY D := by
    intro Y tY hY D hD
    let : MeasurableSpace Y := borel Y
    let : BorelSpace Y := ⟨rfl⟩
    exact hborel hD.measurableSet
  exact winning_of_determined
    (hdet (codeTree μ ε) (codePayoff (H \ A))
      (codePayoff_in_pointclass Γ hpull hclosed hinter hB))
    (hnoI (H \ A) hzero ε hε hεfin)

end PolishSpaceBook.HarringtonCoveringGame
