module

public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset

@[expose] public section

/-! # Finite-branch tests for the Cantor--Bendixson derivative

A binary cylinder meets the derivative of a closed set precisely when its
intersection with that set is infinite. A word has a surviving branch iff
it has extensions in the tree at every later finite level. These are the
geometric ingredients of the numerical derivative test.
-/
namespace PolishSpaceBook
open Set Filter Topology
namespace CantorDerivative

/-- Compactness is used inside the clopen cylinder, not in Baire space. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    For a binary word $s$, compactness shows that $s\in\ClosedTreeCode{\cbderivative{F}}$ holds exactly when
    $F\cap\cyl{s}$ is infinite.
    Indeed, an accumulation point in the open cylinder forces infinitely many points of $F$ there:
    otherwise a smaller neighborhood could exclude all the other finitely many points. Conversely,
    an infinite subset of the compact set $F\cap\cyl{s}$ has an accumulation point in that set. This
    point belongs to $\cbderivative{F}$. Since $F$ is closed, all its accumulation points lie in $F$,
    so this agrees with the derivative defined in §{sec:cantor-bendixson}. The closed-set tree
    representation then proves that $\ClosedTreeCode{\cbderivative{F}}$ is pruned and
    $\TreeBody{\ClosedTreeCode{\cbderivative{F}}}=\cbderivative{F}$.
-/
theorem cylinder_meets_derived_iff {F : Set (ℕ → Bool)} (hF : IsClosed F) (s : List Bool) :
    (cyl s ∩ derivedSet F).Nonempty ↔ (cyl s ∩ F).Infinite := by
  constructor
  · rintro ⟨x, hxs, hx⟩
    exact Set.Infinite.of_accPt (hx.nhds_inter ((isOpen_cyl s).mem_nhds hxs))
  · intro hinf
    have : CompactSpace (ℕ → Bool) := cantor_space_compact
    have hc : IsCompact (cyl s ∩ F) := ((isClosed_cyl s).inter hF).isCompact
    obtain ⟨x, hx, ha⟩ := hinf.exists_accPt_of_subset_isCompact hc Subset.rfl
    exact ⟨x, hx.1, derivedSet_mono _ _ inter_subset_right ha⟩

/-- The canonical pruned code for the derivative, expressed as an infinite-point test. -/
def derivativeTree (T : Set (List Bool)) : Set (List Bool) :=
  {s | (cyl s ∩ treeBody T).Infinite}

theorem derivativeTree_eq (T : Set (List Bool)) :
    derivativeTree T = closedTreeCode (derivedSet (treeBody T)) := by
  ext s
  exact (cylinder_meets_derived_iff (isClosed_treeBody T) s).symm

theorem derivativeTree_isSubtree (T : Set (List Bool)) : IsSubtree (derivativeTree T) := by
  rw [derivativeTree_eq]
  exact closedTreeCode_isSubtree _

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: One effective derivative step
-/
theorem derivativeTree_isPruned (T : Set (List Bool)) : IsPruned (derivativeTree T) := by
  rw [derivativeTree_eq]
  exact closedTreeCode_isPruned _

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: One effective derivative step
-/
theorem derivativeTree_body (T : Set (List Bool)) :
    treeBody (derivativeTree T) = derivedSet (treeBody T) := by
  rw [derivativeTree_eq]
  exact treeBody_closedTreeCode_eq_of_closed (isClosed_derivedSet _)

/-- A purely finite-level condition; no branch is part of its data. -/
def Survives (T : Set (List Bool)) (s : List Bool) : Prop :=
  ∀ n, ∃ t, t.length = s.length + n ∧ s <+: t ∧ t ∈ T

/-- Localize at `s`, retaining its ancestors so that downward closure holds. -/
def localizedTree (T : Set (List Bool)) (s : List Bool) : Set (List Bool) :=
  {t | t ∈ T ∧ (t <+: s ∨ s <+: t)}

theorem localizedTree_isSubtree {T : Set (List Bool)} (hT : IsSubtree T) (s : List Bool) :
    IsSubtree (localizedTree T s) := by
  rintro u t ⟨ht, hts | hst⟩ hut
  · exact ⟨hT ht hut, Or.inl (hut.trans hts)⟩
  · exact ⟨hT ht hut, List.prefix_or_prefix_of_prefix hut hst⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    A word $u$ extends to a branch through $T$ exactly when
    $$\forall n\in\NN\ \exists v\in\finseq{2}\quad
     |v|=|u|+n,\quad u\prefixOf v,\quad v\in T.$$
    The forward implication uses prefixes of the branch. For the reverse implication, apply König's
    lemma to the tree localized above $u$, keeping the ancestors of $u$ so that it is downward closed.
    A finite bound on its height would contradict the displayed condition.
-/
theorem survives_iff {T : Set (List Bool)} (hT : IsSubtree T) (s : List Bool) :
    Survives T s ↔ (cyl s ∩ treeBody T).Nonempty := by
  constructor
  · intro hs
    have hne : (treeBody (localizedTree T s)).Nonempty := by
      by_contra hn
      obtain ⟨n, hn⟩ := konig_binary_tree_bounded_of_empty_body
        (localizedTree_isSubtree hT s) (Set.not_nonempty_iff_eq_empty.mp hn)
      obtain ⟨t, htlen, hst, ht⟩ := hs n
      have hlen : n ≤ t.length := by omega
      have hpre : t.take n <+: t := List.take_prefix _ _
      exact hn (t.take n) (by simp [List.length_take, hlen])
        ⟨hT ht hpre, List.prefix_or_prefix_of_prefix hpre hst⟩
    obtain ⟨x, hx⟩ := hne
    have hcompat := (hx s.length).2
    have heq : seqPrefix x s.length = s := by
      rcases hcompat with h | h
      · exact h.eq_of_length (by simp)
      · exact (h.eq_of_length (by simp)).symm
    exact ⟨x, heq ▸ mem_cyl_seqPrefix x s.length, fun n => (hx n).1⟩
  · rintro ⟨x, hxs, hxT⟩ n
    refine ⟨seqPrefix x (s.length + n), by simp, ?_, hxT _⟩
    rw [← seqPrefix_eq_of_mem_cyl hxs]
    simp only [seqPrefix_length]
    exact seqPrefix_prefixOf_of_le x (by omega)

end CantorDerivative
end PolishSpaceBook
