module

public import PolishSpaceBook.BorelReducibilitySynthesis
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Sum

@[expose] public section

/-!
# The crucial-pair trees in HKL fusion

The level graph is built exactly as in the book: two last-bit copies of the
previous level, joined at their all-zero prefixes. Graph-theoretic properties
use mathlib's `SimpleGraph.IsTree`. The oriented edges are exactly the
zero-prefix pairs with a common finite suffix. A finite path then proves
preservation of eventual equality, conditional on the elementary infinite
pairs being related. `HKLEdgeFusion.lean` produces those related pairs by witnessed analytic-condition
fusion under explicit encoding, presentation, and dense-encounter hypotheses. Coherent node and edge
refinements on the whole tree are proved in `HKLTreeRefinement.lean`.
-/

namespace PolishSpaceBook
open Set Function SimpleGraph

/-- A walk in a disjoint union stays in one summand and lifts to a walk there. -/
theorem walk_sum_lift {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    {u v : V ⊕ W} (p : (G.sum H).Walk u v) :
    match u, v with
    | .inl a, .inl b => ∃ q : G.Walk a b, q.map Embedding.sumInl.toHom = p
    | .inr a, .inr b => ∃ q : H.Walk a b, q.map Embedding.sumInr.toHom = p
    | .inl _, .inr _ => False
    | .inr _, .inl _ => False := by
  induction p with
  | @nil w => cases w <;> exact ⟨.nil, rfl⟩
  | @cons u v w h p ih =>
    cases u <;> cases v <;> cases w <;> simp only [SimpleGraph.sum_adj] at h
    all_goals try contradiction
    all_goals
      obtain ⟨q, hq⟩ := ih
      exact ⟨.cons h q, by simp only [Walk.map_cons, hq]; rfl⟩

theorem isAcyclic_sum {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) : (G.sum H).IsAcyclic := by
  intro u p hp
  cases u with
  | inl a =>
    obtain ⟨q, rfl⟩ := walk_sum_lift G H p
    exact hG q ((Walk.isCycle_map_iff_of_injective Sum.inl_injective).mp hp)
  | inr b =>
    obtain ⟨q, rfl⟩ := walk_sum_lift G H p
    exact hH q ((Walk.isCycle_map_iff_of_injective Sum.inr_injective).mp hp)

/-- Joining two trees by one edge between their disjoint copies gives a tree. -/
theorem isTree_sum_join {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (hH : H.IsTree) (a : V) (b : W) :
    (G.sum H ⊔ SimpleGraph.edge (.inl a) (.inr b)).IsTree := by
  refine ⟨hG.connected.sum_sup_edge hH.connected, ?_⟩
  exact (isAcyclic_sum hG.isAcyclic hH.isAcyclic).sup_edge_of_not_reachable
    (not_reachable_sum_inl_inr a b)

abbrev binaryWord (n : ℕ) := Fin n → Bool

def zeroBinaryWord (n : ℕ) : binaryWord n := fun _ => false

/-- The summand records the last bit, so both copies retain the old prefix. -/
def splitLastBit (n : ℕ) : binaryWord (n + 1) ≃ binaryWord n ⊕ binaryWord n where
  toFun w := if w (Fin.last n) then .inr (Fin.init w) else .inl (Fin.init w)
  invFun := Sum.elim (fun s => Fin.snoc s false) (fun s => Fin.snoc s true)
  left_inv w := by
    cases h : w (Fin.last n) <;> simp only [h, Bool.false_eq_true, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
    all_goals simpa only [h] using Fin.snoc_init_self w
  right_inv w := by cases w <;> simp

/-- Recursive copies plus the new edge between the two zero-prefix vertices. -/
def crucialPairGraph : (n : ℕ) → SimpleGraph (binaryWord n)
  | 0 => ⊥
  | n + 1 => SimpleGraph.comap (splitLastBit n)
      ((crucialPairGraph n).sum (crucialPairGraph n) ⊔
        SimpleGraph.edge (.inl (zeroBinaryWord n)) (.inr (zeroBinaryWord n)))

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    At level $n+1$ there are two copies of the level-$n$ tree, obtained by appending the last bit, joined by the new edge
    $(0^n\concat(0),0^n\concat(1))$. Induction proves that the graph is connected and has no cycles.
-/
theorem crucialPairGraph_isTree (n : ℕ) : (crucialPairGraph n).IsTree := by
  induction n with
  | zero => exact SimpleGraph.IsTree.of_subsingleton
  | succ n ih =>
    exact (SimpleGraph.Iso.comap (splitLastBit n) _).isTree_iff.mpr
      (isTree_sum_join ih ih (zeroBinaryWord n) (zeroBinaryWord n))

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For each $n$, make $2^n$ a finite tree by joining
    $$0^k\concat(0)\concat w\quad\text{to}\quad0^k\concat(1)\concat w
    \qquad(k<n,\ |w|=n-k-1).$$
    Call these the \termdefineas{crucial pair}{crucial pairs}, oriented from $0$ to $1$ at the displayed coordinate.
-/
/-- An oriented crucial pair starts with a zero-prefix joining edge and is
then extended by a common finite suffix. Thus it has the book's form
`0^k 0 w, 0^k 1 w`. -/
inductive CrucialPair : {n : ℕ} → binaryWord n → binaryWord n → Prop
  | join (n : ℕ) : CrucialPair (Fin.snoc (zeroBinaryWord n) false)
      (Fin.snoc (zeroBinaryWord n) true)
  | extend {n : ℕ} {s t : binaryWord n} (h : CrucialPair s t) (b : Bool) :
      CrucialPair (Fin.snoc s b) (Fin.snoc t b)

theorem crucialPairGraph_snoc_same (n : ℕ) (s t : binaryWord n) (b : Bool) :
    (crucialPairGraph (n + 1)).Adj (Fin.snoc s b) (Fin.snoc t b) ↔
      (crucialPairGraph n).Adj s t := by
  cases b <;> simp [crucialPairGraph, splitLastBit, SimpleGraph.edge]

theorem crucialPairGraph_snoc_cross (n : ℕ) (s t : binaryWord n) :
    (crucialPairGraph (n + 1)).Adj (Fin.snoc s false) (Fin.snoc t true) ↔
      s = zeroBinaryWord n ∧ t = zeroBinaryWord n := by
  simp [crucialPairGraph, splitLastBit, SimpleGraph.edge]

theorem CrucialPair.adj {n : ℕ} {s t : binaryWord n} (h : CrucialPair s t) :
    (crucialPairGraph n).Adj s t := by
  induction h with
  | join n => exact (crucialPairGraph_snoc_cross n _ _).mpr ⟨rfl, rfl⟩
  | extend h b ih => exact (crucialPairGraph_snoc_same _ _ _ b).mpr ih

theorem crucialPairGraph_adj_iff (n : ℕ) (s t : binaryWord n) :
    (crucialPairGraph n).Adj s t ↔ CrucialPair s t ∨ CrucialPair t s := by
  constructor
  · intro h
    induction n with
    | zero => exact False.elim h
    | succ n ih =>
      have hs := Fin.snoc_init_self s
      have ht := Fin.snoc_init_self t
      generalize hb : s (Fin.last n) = b at hs
      generalize hc : t (Fin.last n) = c at ht
      rw [← hs, ← ht] at h ⊢
      cases b <;> cases c
      · obtain h | h := ih (Fin.init s) (Fin.init t) ((crucialPairGraph_snoc_same n _ _ false).mp h)
        · exact Or.inl (h.extend false)
        · exact Or.inr (h.extend false)
      · obtain ⟨hzs, hzt⟩ := (crucialPairGraph_snoc_cross n _ _).mp h
        rw [hzs, hzt]
        exact Or.inl (.join n)
      · obtain ⟨hzt, hzs⟩ := (crucialPairGraph_snoc_cross n _ _).mp h.symm
        rw [hzs, hzt]
        exact Or.inr (.join n)
      · obtain h | h := ih (Fin.init s) (Fin.init t) ((crucialPairGraph_snoc_same n _ _ true).mp h)
        · exact Or.inl (h.extend true)
        · exact Or.inr (h.extend true)
  · rintro (h | h)
    · exact h.adj
    · exact h.adj.symm

/-- Put one binary digit before an infinite tail. -/
def binaryCons (b : Bool) (c : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | k + 1 => c k

/-- Attach an infinite common tail to a finite word. -/
def binaryWordTail {n : ℕ} (s : binaryWord n) (c : ℕ → Bool) : ℕ → Bool :=
  fun k => if h : k < n then s ⟨k, h⟩ else c (k - n)

theorem binaryWordTail_snoc {n : ℕ} (s : binaryWord n) (b : Bool) (c : ℕ → Bool) :
    binaryWordTail (Fin.snoc s b) c = binaryWordTail s (binaryCons b c) := by
  funext k
  by_cases hk : k < n
  · have hk' : k < n + 1 := by omega
    simp only [binaryWordTail, dite_eq_left hk, dite_eq_left hk']
    exact @Fin.snoc_castSucc n (fun _ => Bool) b s ⟨k, hk⟩
  · by_cases hkn : k = n
    · subst k
      simp only [binaryWordTail, Nat.lt_succ_self, dite_eq_left, lt_self_iff_false,
        Nat.sub_self, binaryCons]
      exact @Fin.snoc_last n (fun _ => Bool) b s
    · have hk' : ¬ k < n + 1 := by omega
      have heq : k - n = (k - (n + 1)) + 1 := by omega
      simp only [binaryWordTail, dite_eq_right hk, dite_eq_right hk', heq, binaryCons]

/-- After appending a common infinite tail, every finite crucial edge has
the elementary infinite form used in the fusion argument. -/
theorem CrucialPair.append_tail {n : ℕ} {s t : binaryWord n} (h : CrucialPair s t)
    (c : ℕ → Bool) :
    ∃ k d, binaryWordTail s c = binaryWordTail (zeroBinaryWord k) (binaryCons false d) ∧
      binaryWordTail t c = binaryWordTail (zeroBinaryWord k) (binaryCons true d) := by
  induction h generalizing c with
  | join n => exact ⟨n, c, binaryWordTail_snoc _ _ _, binaryWordTail_snoc _ _ _⟩
  | extend h b ih =>
    rw [binaryWordTail_snoc, binaryWordTail_snoc]
    exact ih (binaryCons b c)

/-- Connectedness turns the verified elementary edges into an equivalence
between any two finite prefixes with the same infinite tail. -/
theorem related_common_tail_of_crucial_pairs {X : Type*} (E : Setoid X)
    (π : (ℕ → Bool) → X)
    (hedge : ∀ k c, E.r (π (binaryWordTail (zeroBinaryWord k) (binaryCons false c)))
      (π (binaryWordTail (zeroBinaryWord k) (binaryCons true c))))
    (n : ℕ) (s t : binaryWord n) (c : ℕ → Bool) :
    E.r (π (binaryWordTail s c)) (π (binaryWordTail t c)) := by
  have horiented {s t : binaryWord n} (h : CrucialPair s t) :
      E.r (π (binaryWordTail s c)) (π (binaryWordTail t c)) := by
    obtain ⟨k, d, hs, ht⟩ := h.append_tail c
    rw [hs, ht]
    exact hedge k d
  have hadj {s t : binaryWord n} (h : (crucialPairGraph n).Adj s t) :
      E.r (π (binaryWordTail s c)) (π (binaryWordTail t c)) := by
    obtain h | h := (crucialPairGraph_adj_iff n s t).mp h
    · exact horiented h
    · exact E.symm (horiented h)
  obtain ⟨p⟩ := (crucialPairGraph_isTree n).connected s t
  induction p with
  | nil => exact E.refl _
  | cons h p ih => exact E.trans (hadj h) ih

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Finally, if $a\mathrel{\EventualEqualityER}b$, choose $m$ after their last disagreement and write
    $a=s\concat c$, $b=t\concat c$ with $s,t\in2^m$. The crucial-pair tree on $2^m$ has a finite path from $s$ to $t$.
    Appending the same infinite tail $c$ to each vertex of that path gives a finite chain of pairs of the preceding
    special form, with either orientation. Symmetry and transitivity of $E$ give $\pi(a)\mathrel E\pi(b)$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    This proves both directions of the reduction on Baire space. For a general Polish $X$, take a closed
    $F\IncludedIn\BaireSpace$ and a continuous Borel isomorphism from $F$ onto $X$, as constructed in
    §{sec:closed-presentation-baire}. Pull $E$ back to $F$ and extend it to Baire space by putting all points outside
    $F$ into one new class. This extension is Borel and nonsmooth: a complete Borel invariant for it would restrict
    to one for $E$. Apply the Baire-space result. The inverse image of $F$ under the resulting embedding is closed
    and $\EventualEqualityER$-invariant. It is nonempty, since otherwise all images would be equivalent. Every nonempty
    closed $\EventualEqualityER$-invariant subset of Cantor space is the whole space: changing increasingly long
    prefixes of one member approximates any prescribed binary sequence. Hence the embedding takes values in $F$.
    Composing with the continuous Borel isomorphism onto $X$ preserves continuity, injectivity, and the reduction
    equivalence.
-/
/-- The forward `E₀` implication of HKL follows once fusion has established
the elementary crucial pairs. This lemma does not assume the forward
implication itself. -/
theorem e0_preserved_of_crucial_pairs {X : Type*} (E : Setoid X)
    (π : (ℕ → Bool) → X)
    (hedge : ∀ k c, E.r (π (binaryWordTail (zeroBinaryWord k) (binaryCons false c)))
      (π (binaryWordTail (zeroBinaryWord k) (binaryCons true c))))
    {a b : ℕ → Bool} (hab : E0 a b) : E.r (π a) (π b) := by
  obtain ⟨n, hn⟩ := hab
  let s : binaryWord n := fun i => a i.val
  let t : binaryWord n := fun i => b i.val
  let c : ℕ → Bool := fun k => a (k + n)
  have hs : binaryWordTail s c = a := by
    funext k
    by_cases hk : k < n
    · simp [binaryWordTail, hk, s]
    · simp [binaryWordTail, hk, c, Nat.sub_add_cancel (by omega : n ≤ k)]
  have ht : binaryWordTail t c = b := by
    funext k
    by_cases hk : k < n
    · simp [binaryWordTail, hk, t]
    · simp only [binaryWordTail, dite_eq_right hk, c, Nat.sub_add_cancel (by omega : n ≤ k)]
      exact hn k (by omega)
  have h := related_common_tail_of_crucial_pairs E π hedge n s t c
  rwa [hs, ht] at h

end PolishSpaceBook
