module

public import PolishSpaceBook.MartinMonkFlip
public import PolishSpaceBook.WadgeStrategyReduction

@[expose] public section

/-!
# The simultaneous array of Wadge boards

The time coordinate decreases in every recursive call. Causality makes the
zero-padded temporary input irrelevant once the full next row is available.
The finite dependence cone proves continuity and independence of earlier bits.
-/

noncomputable section
namespace PolishSpaceBook.MartinMonk
open Set Filter Topology

abbrev Baire := ℕ → ℕ

def StrictlyCausal (f : Baire → Baire) : Prop :=
  ∀ t x y, (∀ k < t, x k = y k) → f x t = f y t

lemma firstReductionMap_causal (σ : WadgeGame.FirstStrategy) :
    StrictlyCausal (WadgeGame.firstReductionMap σ) := by
  intro t x y h
  exact WadgeGame.againstI_prefix σ h (2 * t) (by omega)

variable (F : ℕ → Bool → Baire → Baire)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For each binary sequence $z\in\CantorSpace$, play all games
    $$G^z_n :=
    \begin{cases}
    G_W(A_n,A_{n+1}), & z(n)=0,\\
    G_W(A_n,\SetDifference{\BaireSpace}{A_{n+1}}), & z(n)=1
    \end{cases}
    \qquad (n\in\omega)
    $$
    simultaneously, using no passes. Write $x^z_n$ for I's output on board $n$, and let II's output there be
    $x^z_{n+1}$. To define the array without circularity, recurse on time $t$. Once all moves at earlier times
    are known, put
    $$
    \begin{aligned}
    y^z_{n,t}(k)&=
    \begin{cases}
    x^z_{n+1}(k),&k<t,\\
    0,&k\ge t,
    \end{cases}\\
    x^z_n(t)&=g^{z(n)}_n(y^z_{n,t})(t).
    \end{aligned}
    $$
    The temporary zeros do not affect the last value, since it depends only on coordinates before $t$.
    Consequently the completed rows satisfy
    $$x^z_n=g^{z(n)}_n(x^z_{n+1}).$$
    Thus every board follows the chosen winning strategy, with II's output equal to $x^z_{n+1}$.
-/
def boardMove (z : Cantor) (t n : ℕ) : ℕ :=
  F n (z n) (fun k => if h : k < t then boardMove z k (n + 1) else 0) t
termination_by t

def row (z : Cantor) (n : ℕ) : Baire := fun t => boardMove F z t n

variable (hF : ∀ n b, StrictlyCausal (F n b))
include hF

lemma row_eq (z : Cantor) (n : ℕ) : row F z n = F n (z n) (row F z (n + 1)) := by
  funext t
  change boardMove F z t n = _
  rw [boardMove]
  apply hF n (z n) t
  intro k hk
  simp only [dite_eq_left hk, row]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Induction on $t$ shows that $x^z_n(t)$ depends only on $z(n),\ldots,z(n+t)$: the current choice uses $z(n)$,
    and a next-board move at time $k<t$ depends only on bits from $n+1$ through $n+1+k\le n+t$.
    In particular, the whole row on board $n$ depends only on the tail starting at $n$.
    Agreement on a sufficiently long finite prefix of $z$ fixes any prescribed finite prefix of that row,
    so every map $z\mapsto x^z_n$ is continuous.
-/
/-- The move at time t on board n sees only bits n through n+t. -/
lemma boardMove_cone (t : ℕ) : ∀ n (z w : Cantor),
    (∀ k, n ≤ k → k ≤ n + t → z k = w k) → boardMove F z t n = boardMove F w t n := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro n z w heq
    rw [boardMove, boardMove, heq n le_rfl (by omega)]
    apply hF n (w n) t
    intro k hk
    simp only [dite_eq_left hk]
    apply ih k hk (n + 1) z w
    intro j hj hjt
    exact heq j (by omega) (by omega)

lemma row_tail {n : ℕ} {z w : Cantor} (h : ∀ k, n ≤ k → z k = w k) :
    row F z n = row F w n := by
  funext t
  exact boardMove_cone F hF t n z w (fun k hk _ => h k hk)

lemma row_flip_later {n m : ℕ} (h : n < m) (z : Cantor) :
    row F (flip n z) m = row F z m := by
  apply row_tail F hF
  intro k hk
  exact flip_other (by omega) z

lemma row_continuous (n : ℕ) : Continuous (fun z => row F z n) := by
  apply continuous_pi
  intro t
  rw [continuous_iff_continuousAt]
  intro z
  apply Filter.EventuallyEq.continuousAt (y := row F z n t)
  filter_upwards [(isOpen_cyl (seqPrefix z (n + t + 1))).mem_nhds
    (mem_cyl_seqPrefix z _)] with w hw
  apply boardMove_cone F hF t n w z
  intro k _ hk
  exact (hw k (by simpa using hk)).trans (seqPrefix_get z _)

variable (A : ℕ → Set Baire)
variable (hrel : ∀ n b y, F n b y ∈ A n ↔
  if b then y ∈ A (n + 1) else y ∉ A (n + 1))
include hrel

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Define truth values
    $$\varepsilon_n(z)=1 \quad\Longleftrightarrow\quad x^z_n\in A_n.$$
    Since I wins every board, the displayed equivalences give
    $$
    \varepsilon_n(z)=
    \begin{cases}
    1-\varepsilon_{n+1}(z), & z(n)=0,\\
    \varepsilon_{n+1}(z), & z(n)=1.
    \end{cases}
    $$
-/
lemma row_relation (n : ℕ) (z : Cantor) : row F z n ∈ A n ↔
    if z n then row F z (n + 1) ∈ A (n + 1) else row F z (n + 1) ∉ A (n + 1) := by
  rw [row_eq F hF z n]
  exact hrel n (z n) _

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    The set $D$ is a flip set. Indeed, if $z'$ is obtained from $z$ by changing only coordinate $n$, the tail dependence
    leaves $x^z_{n+1}$ unchanged. The two recurrence clauses then give $\varepsilon_n(z')=1-\varepsilon_n(z)$.
    For $m<n$, the reals $z$ and $z'$ have the same
    $m$-th bit, so the recurrence propagates this change down to $\varepsilon_0(z')=1-\varepsilon_0(z)$. Thus the
    homeomorphism $h_n$ that flips coordinate $n$ sends $D$ to its complement.
-/
/-- Toggling a board choice reverses the truth value there and on every earlier board. -/
lemma row_flip_membership (n : ℕ) (z : Cantor) : ∀ m ≤ n,
    row F (flip n z) m ∈ A m ↔ row F z m ∉ A m := by
  intro m hm
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [row_relation F hF A hrel n (flip n z), row_relation F hF A hrel n z,
      row_flip_later F hF (by omega : n < n + 1), flip_same]
    cases z n <;> simp
  | of_succ m hm ih =>
    rw [row_relation F hF A hrel m (flip n z), row_relation F hF A hrel m z,
      flip_other (by omega)]
    cases z m <;> simp_all

def diagonal : Set Cantor := {z | row F z 0 ∈ A 0}

lemma diagonal_flip : IsFlipSet (diagonal F A) := by
  intro n z
  exact row_flip_membership F hF A hrel n z 0 (Nat.zero_le n)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Set
    $$D:=\{z\in\CantorSpace:\varepsilon_0(z)=1\}.$$
    Since $D$ is the inverse image of the Borel set $A_0$ under the continuous map $z\mapsto x^z_0$,
    it is Borel and therefore has the \termuse{Baire property}.
-/
omit hrel in
lemma diagonal_measurable (hA : MeasurableSet (A 0)) : MeasurableSet (diagonal F A) :=
  hA.preimage (row_continuous F hF 0).measurable

/-- Causal maps with the two opposing truth recurrences cannot exist over a Borel first set. -/
theorem no_causal_array (hA : MeasurableSet (A 0)) : False :=
  flip_not_baire (diagonal_flip F hF A hrel) (diagonal_measurable F hF A hA).baireMeasurableSet

end PolishSpaceBook.MartinMonk
