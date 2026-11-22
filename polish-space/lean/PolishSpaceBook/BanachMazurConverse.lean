module

public import PolishSpaceBook.BanachMazurRefinement
public import Mathlib.Topology.Baire.CompleteMetrizable

@[expose] public section

/-!
# The Banach–Mazur converse

Iterate countable disjoint response families. A point surviving all levels
uniquely determines a coherent legal play, so a winning II strategy forces the
payoff to miss a relatively residual set.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Topology TopologicalSpace Filter
open scoped Classical
variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]

/-- A finite history together with the open set in which its next move must lie. -/
structure Position (X : Type*) [TopologicalSpace X] where
  history : List (Move X)
  last : Move X

def rootPosition (W : Move X) : Position X := ⟨[], W⟩

def family (σ : Strategy X) (p : Position X) : ResponseFamily σ p.history p.last :=
  responseFamily σ p.history p.last

def childPosition (σ : Strategy X) (p : Position X) (i : ℕ) : Position X :=
  ⟨p.history ++ [(family σ p).moves i], (σ p.history ((family σ p).moves i)).toMove⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \emph{Proof of $(\Rightarrow)$.} Let $\sigma$ be a winning strategy for II. We construct countable families
    $\mathcal F_n$ of legal $\sigma$-positions after $n$ complete rounds. Start with
    $\mathcal F_0=\{\emptySeq\}$, the empty history, and associate to it the current open set $W$.
    For any other position $p$, write $V(p)$ for its last response; put $V(\emptySeq)=W$.

    For each $p\in\mathcal F_n$, apply the \termuse{disjoint response refinement} lemma inside $V(p)$.
    Use as $B_j$ the basic open sets with $\Closure{B_j}\IncludedIn V(p)$, and as $R_j$ the responses prescribed
    by $\sigma$ when I plays $B_j$ after $p$. Keep the extended position $(p,B_j,R_j)$ precisely when the rule
    accepts $R_j$. Let $\mathcal F_{n+1}$ consist of all these extensions. Every extension is legal, and each
    family is countable. The responses from one parent are disjoint by the lemma. Responses from different
    parents lie inside disjoint parent responses, so induction shows that the sets $V(p)$, for
    $p\in\mathcal F_n$, are pairwise disjoint at every level.
-/
def positions (σ : Strategy X) (W : Move X) : ℕ → Set (Position X)
  | 0 => {rootPosition W}
  | n + 1 => {q | ∃ p ∈ positions σ W n, ∃ i ∈ (family σ p).selected,
      q = childPosition σ p i}

def levelOpen (σ : Strategy X) (W : Move X) (n : ℕ) : Set X :=
  ⋃ p ∈ positions σ W n, p.last.openSet

lemma child_subset (σ : Strategy X) (p : Position X) (i : ℕ) :
    (childPosition σ p i).last.openSet ⊆ p.last.openSet :=
  subset_closure.trans ((σ p.history ((family σ p).moves i)).closure_subset.trans
    (subset_closure.trans ((family σ p).closure_subset i)))

lemma positions_pairwise (σ : Strategy X) (W : Move X) (n : ℕ) :
    (positions σ W n).Pairwise (fun p q => Disjoint p.last.openSet q.last.openSet) := by
  induction n with
  | zero => exact Set.pairwise_singleton _ _
  | succ n ih =>
    intro p hp q hq hpq
    obtain ⟨a, ha, i, hi, rfl⟩ := hp
    obtain ⟨b, hb, j, hj, rfl⟩ := hq
    by_cases hab : a = b
    · subst b
      have hij : i ≠ j := fun h => hpq (h ▸ rfl)
      exact (family σ a).disjoint hi hj hij
    · exact (ih ha hb hab).mono (child_subset σ a i) (child_subset σ b j)

lemma position_unique (σ : Strategy X) (W : Move X) {n : ℕ} {p q : Position X}
    (hp : p ∈ positions σ W n) (hq : q ∈ positions σ W n) {x : X}
    (hxp : x ∈ p.last.openSet) (hxq : x ∈ q.last.openSet) : p = q := by
  by_contra h
  exact Set.disjoint_left.mp (positions_pairwise σ W n hp hq h) hxp hxq

lemma positions_countable (σ : Strategy X) (W : Move X) (n : ℕ) :
    (positions σ W n).Countable := by
  induction n with
  | zero => exact countable_singleton _
  | succ n ih =>
    have hsub : positions σ W (n + 1) ⊆ ⋃ p ∈ positions σ W n, range (childPosition σ p) := by
      rintro q ⟨p, hp, i, _, rfl⟩
      exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, mem_range_self i⟩⟩
    exact (ih.biUnion fun p _ => countable_range (childPosition σ p)).mono hsub

lemma levelOpen_zero (σ : Strategy X) (W : Move X) : levelOpen σ W 0 = W.openSet := by
  simp [levelOpen, positions, rootPosition]

lemma levelOpen_isOpen (σ : Strategy X) (W : Move X) (n : ℕ) : IsOpen (levelOpen σ W n) :=
  isOpen_iUnion fun p => isOpen_iUnion fun _ => p.last.isOpen

lemma levelOpen_succ_subset (σ : Strategy X) (W : Move X) (n : ℕ) :
    levelOpen σ W (n + 1) ⊆ levelOpen σ W n := by
  intro x hx
  obtain ⟨q, hq⟩ := mem_iUnion.mp hx
  obtain ⟨⟨p, hp, i, _, rfl⟩, hxq⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, child_subset σ p i hxq⟩⟩

lemma levelOpen_subset_initial (σ : Strategy X) (W : Move X) (n : ℕ) :
    levelOpen σ W n ⊆ W.openSet := by
  rw [← levelOpen_zero σ W]
  exact (antitone_nat_of_succ_le (levelOpen_succ_subset σ W)) (Nat.zero_le n)

lemma levelOpen_subset_closure_succ (σ : Strategy X) (W : Move X) (n : ℕ) :
    levelOpen σ W n ⊆ closure (levelOpen σ W (n + 1)) := by
  intro x hx
  obtain ⟨p, hp⟩ := mem_iUnion.mp hx
  obtain ⟨hp, hxp⟩ := mem_iUnion.mp hp
  apply closure_mono (s := ⋃ i ∈ (family σ p).selected,
    (σ p.history ((family σ p).moves i)).openSet) ?_ ((family σ p).dense hxp)
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨hi, hyi⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨childPosition σ p i, mem_iUnion.mpr ⟨⟨p, hp, i, hi, rfl⟩, hyi⟩⟩

lemma levelOpen_dense (σ : Strategy X) (W : Move X) (n : ℕ) :
    W.openSet ⊆ closure (levelOpen σ W n) := by
  induction n with
  | zero => rw [levelOpen_zero]; exact subset_closure
  | succ n ih =>
    exact ih.trans (closure_minimal (levelOpen_subset_closure_succ σ W n) isClosed_closure)

/-- Pick the unique node whose last response contains the surviving point. -/
def pointPosition (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) : Position X :=
  (mem_iUnion.mp (hx n)).choose

lemma pointPosition_mem (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) :
    pointPosition σ W x hx n ∈ positions σ W n ∧
      x ∈ (pointPosition σ W x hx n).last.openSet := by
  obtain ⟨hp, hxp⟩ := mem_iUnion.mp (mem_iUnion.mp (hx n)).choose_spec
  exact ⟨hp, hxp⟩

lemma pointPosition_zero (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) : pointPosition σ W x hx 0 = rootPosition W :=
  (pointPosition_mem σ W x hx 0).1

lemma pointPosition_child (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) :
    ∃ i ∈ (family σ (pointPosition σ W x hx n)).selected,
      pointPosition σ W x hx (n + 1) = childPosition σ (pointPosition σ W x hx n) i := by
  obtain ⟨p, hp, i, hi, heq⟩ := (pointPosition_mem σ W x hx (n + 1)).1
  have hxp : x ∈ p.last.openSet := child_subset σ p i
    (heq ▸ (pointPosition_mem σ W x hx (n + 1)).2)
  have hpEq := position_unique σ W hp (pointPosition_mem σ W x hx n).1 hxp
    (pointPosition_mem σ W x hx n).2
  subst p
  exact ⟨i, hi, heq⟩


/-- The index of the selected successor containing the surviving point. -/
def pointIndex (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) : ℕ :=
  (pointPosition_child σ W x hx n).choose

def pointMove (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) : Move X :=
  (family σ (pointPosition σ W x hx n)).moves (pointIndex σ W x hx n)

lemma pointPosition_succ (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) :
    pointPosition σ W x hx (n + 1) =
      childPosition σ (pointPosition σ W x hx n) (pointIndex σ W x hx n) :=
  (pointPosition_child σ W x hx n).choose_spec.2

lemma pointPosition_history (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) :
    (pointPosition σ W x hx n).history = (List.range n).map (pointMove σ W x hx) := by
  induction n with
  | zero => rw [pointPosition_zero]; rfl
  | succ n ih =>
    rw [pointPosition_succ]
    change (pointPosition σ W x hx n).history ++ [pointMove σ W x hx n] = _
    rw [ih, List.range_succ, List.map_append]
    rfl

lemma pointPosition_last_succ (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) (n : ℕ) :
    (pointPosition σ W x hx (n + 1)).last.openSet =
      (responseAt σ (pointMove σ W x hx) n).openSet := by
  rw [pointPosition_succ]
  exact congrArg (fun h => (σ h (pointMove σ W x hx n)).openSet)
    (pointPosition_history σ W x hx n)

lemma pointMove_legal (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) : Legal W.openSet σ (pointMove σ W x hx) := by
  have hcl (n : ℕ) : closure (pointMove σ W x hx n).openSet ⊆
      (pointPosition σ W x hx n).last.openSet :=
    (family σ (pointPosition σ W x hx n)).closure_subset (pointIndex σ W x hx n)
  constructor
  · have h0 := hcl 0
    rw [pointPosition_zero] at h0
    exact subset_closure.trans h0
  · intro n
    simpa only [pointPosition_last_succ] using hcl (n + 1)

lemma pointMove_outcome (σ : Strategy X) (W : Move X) (x : X)
    (hx : ∀ n, x ∈ levelOpen σ W n) : IsOutcome σ (pointMove σ W x hx) x := by
  intro n
  apply subset_closure
  rw [← pointPosition_last_succ]
  exact (pointPosition_mem σ W x hx (n + 1)).2

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Put
    $$D_n:=\bigcup_{p\in\mathcal F_n}V(p),\qquad D:=\bigcap_n D_n.$$
    Here $D_0=W$, and every $D_n$ is open. Each parent's selected responses have dense union in that parent,
    so $D_n\IncludedIn\Closure{D_{n+1}}$. Inductively, every $D_n$ is dense in $W$.
    The Baire category theorem makes $D$ dense in $W$, and $D$ is a $\Gdelta$ set.
    Moreover, each $\SetDifference{W}{D_n}$ is relatively closed and nowhere dense in $W$, so
    $\SetDifference{W}{D}$ is meager in $W$.
-/
/-- The surviving points form a relatively residual Gδ set. -/
theorem surviving_residual (σ : Strategy X) (W : Move X) :
    (Subtype.val ⁻¹' (⋂ n, levelOpen σ W n) : Set W.openSet) ∈ residual W.openSet := by
  rw [preimage_iInter]
  apply countable_iInter_mem.mpr
  intro n
  apply residual_of_dense_open ((levelOpen_isOpen σ W n).preimage continuous_subtype_val)
  intro x
  exact W.isOpen.isOpenMap_subtype_val.preimage_closure_subset_closure_preimage
    (levelOpen_dense σ W n x.property)

theorem surviving_isGδ (σ : Strategy X) (W : Move X) :
    IsGδ (⋂ n, levelOpen σ W n) := IsGδ.iInter_of_isOpen (levelOpen_isOpen σ W)

theorem surviving_dense [CompleteSpace X] (σ : Strategy X) (W : Move X) :
    Dense (Subtype.val ⁻¹' (⋂ n, levelOpen σ W n) : Set W.openSet) := by
  let : BaireSpace W.openSet := W.isOpen.baireSpace
  exact dense_of_mem_residual (surviving_residual σ W)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    If $x\in D$, disjointness gives a unique $p_n\in\mathcal F_n$ with $x\in V(p_n)$.
    The current open set of the parent of $p_{n+1}$ also contains $x$, so uniqueness forces that parent to be $p_n$.
    Thus these positions fit together into one infinite legal $\sigma$-play. Its response at round $n$ is
    $V(p_{n+1})$, which contains $x$, so the unique outcome of this play is $x$.
    Since $\sigma$ is winning, $x\notin A$. Hence $A\cap W\IncludedIn\SetDifference{W}{D}$ is meager in $W$.
    \end{proof}
-/
/-- A winning strategy cannot have a surviving point in its opponent's payoff. -/
theorem surviving_disjoint [CompleteSpace X] {A : Set X} (W : Move X) {σ : Strategy X}
    (hσ : Winning A W.openSet σ) : Disjoint A (⋂ n, levelOpen σ W n) := by
  rw [Set.disjoint_left]
  intro x hxA hx
  have hxall := mem_iInter.mp hx
  have hp := pointMove_legal σ W x hxall
  obtain ⟨y, hy, hyA⟩ := hσ _ hp
  obtain ⟨z, _, hu⟩ := exists_unique_outcome hp
  have hyx : y = x := (hu y hy).trans (hu x (pointMove_outcome σ W x hxall)).symm
  exact hyA (hyx.symm ▸ hxA)

/-- The complement of the residual surviving set is meagre in the initial open set. -/
theorem isMeagre_of_winning [CompleteSpace X] {A : Set X} (W : Move X) {σ : Strategy X}
    (hσ : Winning A W.openSet σ) : IsMeagre (Subtype.val ⁻¹' A : Set W.openSet) := by
  apply Filter.mem_of_superset (surviving_residual σ W)
  intro x hx hxA
  exact Set.disjoint_left.mp (surviving_disjoint W hσ) hxA hx

/-- The Banach–Mazur–Oxtoby equivalence for the complete-metric game. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Banach–Mazur–Oxtoby
-/
theorem winning_iff_isMeagre [CompleteSpace X] {A : Set X} (W : Move X) :
    (∃ σ : Strategy X, Winning A W.openSet σ) ↔
      IsMeagre (Subtype.val ⁻¹' A : Set W.openSet) :=
  ⟨fun ⟨_, hσ⟩ => isMeagre_of_winning W hσ, exists_winning_of_isMeagre W⟩

end PolishSpaceBook.BanachMazurGame
