module

public import PolishSpaceBook.GameTreeCoverings
public import PolishSpaceBook.EventuallyBijectiveSystem

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Stable finite levels in a tower of controlled game coverings

Each finite level is an inverse system with eventually bijective bonding maps.
Taking a shorter prefix commutes with every bonding map, so compatible level
families can be truncated coherently. Move alphabets may vary with the stage.
-/
noncomputable section
namespace PolishSpaceBook.TreeGames
open Set Function
universe u v
namespace GameTree
variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-- Truncation of a legal position, with its precise shorter level retained. -/
def takeLevel (T : GameTree M) {n : ℕ} (s : T.Level n) (m : ℕ) (hm : m ≤ n) : T.Level m :=
  ⟨⟨s.val.val.take m,T.subtree s.val.property (List.take_prefix _ _)⟩, by
    simp only [List.length_take,s.property,Nat.min_eq_left hm]⟩

omit [TopologicalSpace M] in
@[simp] theorem takeLevel_prefix (T : GameTree M) (x : T.Play) (n m : ℕ) (hm : m ≤ n) :
    T.takeLevel (T.prefixLevel x n) m hm = T.prefixLevel x m := by
  apply Subtype.ext
  apply Subtype.ext
  exact seqPrefix_take_of_le x.val hm

/-- A causal branch map determines prefix-compatible maps on every legal level,
using branch extension to test an arbitrary finite position. -/
theorem ControlledCovering.nodeMap_take {S : GameTree N} {T : GameTree M} {k n : ℕ}
    (C : ControlledCovering S T k) (s : S.Level n) (m : ℕ) (hm : m ≤ n) :
    T.takeLevel (C.nodeMap n s) m hm = C.nodeMap m (S.takeLevel s m hm) := by
  obtain ⟨x,hx⟩ := (S.position_iff_prefix_play s.val.val).mp s.val.property
  have he : S.prefixLevel x n = s := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [prefixLevel,prefixPosition,s.property] using seqPrefix_eq_of_mem_cyl hx
  rw [← he, ← C.prefix_project, takeLevel_prefix, takeLevel_prefix, C.prefix_project]

/-- A sequence of coverings whose preserved opening grows by one at each step. -/
structure ControlledTower (A : ℕ → Type u) [∀ i, TopologicalSpace (A i)] (k : ℕ) where
  tree : ∀ i, GameTree (A i)
  covering : ∀ i, ControlledCovering (tree (i+1)) (tree i) (k+i)

namespace ControlledTower
variable {A : ℕ → Type u} [∀ i, TopologicalSpace (A i)] {k : ℕ}
variable (C : ControlledTower A k)

/-- The inverse system of nodes at one fixed finite level. -/
@[reducible] def levels (n : ℕ) : NatInverseSystem where
  Obj i := (C.tree i).Level n
  step i := (C.covering i).nodeMap n

abbrev StableLevel (n : ℕ) := (C.levels n).Limit

/-- Beyond a stable stage every later map is already bijective on this level. -/
theorem levels_eventually_bijective (n j : ℕ) (hj : n ≤ k+j) :
    ∀ i ≥ j, Function.Bijective ((C.levels n).step i) := by
  intro i hi
  exact (C.covering i).initial_bijective n (by omega)

/-- Evaluation identifies the stabilized level with any sufficiently late finite level. -/
theorem level_evaluation_bijective (n j : ℕ) (hj : n ≤ k+j) :
    Function.Bijective (fun s : C.StableLevel n => s.val j) :=
  NatInverseSystem.evaluation_bijective (C.levels_eventually_bijective n j hj)

/-- Coherent truncation of an entire stable level. -/
def truncate {n : ℕ} (s : C.StableLevel n) (m : ℕ) (hm : m ≤ n) : C.StableLevel m := by
  refine ⟨fun i => (C.tree i).takeLevel (s.val i) m hm, ?_⟩
  intro i
  change (C.covering i).nodeMap m ((C.tree (i+1)).takeLevel (s.val (i+1)) m hm) = _
  rw [← ControlledCovering.nodeMap_take]
  exact congrArg (fun t => (C.tree i).takeLevel t m hm) (s.property i)

/-- Equality at one stable component is equality of the whole coherent level. -/
theorem stableLevel_ext {n j : ℕ} (hj : n ≤ k+j) {s t : C.StableLevel n}
    (h : s.val j = t.val j) : s = t :=
  (C.level_evaluation_bijective n j hj).injective h

/-- Read a coherent level as a word of simultaneous stage moves. -/
def word {n : ℕ} (s : C.StableLevel n) : List (∀ i, A i) :=
  List.ofFn (fun j : Fin n => fun i => (s.val i).val.val[j.val]'(by
    rw [(s.val i).property]
    exact j.isLt))

@[simp] theorem word_length {n : ℕ} (s : C.StableLevel n) : (C.word s).length = n := by
  simp [word]

/-- The component word is exactly the corresponding legal position. -/
theorem word_component {n : ℕ} (s : C.StableLevel n) (i : ℕ) :
    (C.word s).map (fun a => a i) = (s.val i).val.val := by
  apply List.ext_getElem
  · simp only [List.length_map,word_length,(s.val i).property]
  · intro j hj hj'
    simp [word]

/-- Truncating coherent levels truncates their simultaneous words. -/
theorem word_truncate {n : ℕ} (s : C.StableLevel n) (m : ℕ) (hm : m ≤ n) :
    C.word (C.truncate s m hm) = (C.word s).take m := by
  apply List.ext_getElem
  · simp [word_length,hm]
  · intro j hj hj'
    funext i
    simp [word,truncate,takeLevel]

/-- A node can be extended by choosing a successor at a sufficiently late stage,
then using the stable-level bijection to recover every component. -/
theorem stableLevel_successor {n : ℕ} (s : C.StableLevel n) :
    ∃ t : C.StableLevel (n+1), C.truncate t n (by omega) = s := by
  let j := n+1
  let v := (C.tree j).child (s.val j).val ((C.tree j).defaultPolicy (s.val j).val)
  have hv : v.val.length = n+1 := by
    simp only [v,child,List.length_append,List.length_singleton,(s.val j).property]
  obtain ⟨t,ht⟩ := (C.level_evaluation_bijective (n+1) j (by dsimp [j]; omega)).surjective ⟨v,hv⟩
  refine ⟨t,C.stableLevel_ext (j := j) (by dsimp [j]; omega) ?_⟩
  change (C.tree j).takeLevel (t.val j) n (Nat.le_succ n) = s.val j
  change t.val j = ⟨v,hv⟩ at ht
  rw [ht]
  apply Subtype.ext
  apply Subtype.ext
  change (v.val.take n) = (s.val j).val.val
  dsimp [v,child]
  conv_lhs => arg 1; rw [← (s.val j).property]
  simp

/-- Legal finite limit positions are the stabilized coherent levels. -/
def limitNodes : Set (List (∀ i, A i)) := {s | ∃ n, ∃ t : C.StableLevel n, s = C.word t}

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Because the covering from $T_{i+1}$ to $T_i$ is bijective through level $k+i$, we may identify the
    trees through those levels. More explicitly, a level-$m$ node is represented by a coherent family
    $\Sequence{s_i}{i\in\omega}$ of level-$m$ nodes: each bonding prefix map sends $s_{i+1}$ to $s_i$.
    Evaluation at any stage $j$ with $m\le k+j$ is bijective. Earlier coordinates are finite projections,
    and later coordinates are obtained by the unique inverses of the bijective bonding maps.
    Truncation commutes with these maps. Use the coherent families as the levels of $T_\infty$, with
    coordinatewise truncation as the prefix operation. This gives a tree on the product of the move sets:
    a finite word records at each move the corresponding move in every $T_i$. We use actual coherent families,
    so no literal equality of the different stage alphabets is required. Prefix closure follows from compatible truncation.
    To extend a node of length $m$, choose a stage beyond
    $m+1$, choose a legal child there, and recover its coherent family by finite projections and the unique later
    inverse maps. The recovered family truncates to the original node. Thus this tree has no terminal nodes.
-/
/-- The stabilized finite positions form a tree with no terminal nodes. -/
def limitTree : GameTree (∀ i, A i) where
  nodes := C.limitNodes
  subtree := by
    intro s t ht hst
    obtain ⟨n,v,rfl⟩ := ht
    have hm : s.length ≤ n := by simpa only [word_length] using hst.length_le
    exact ⟨s.length,C.truncate v s.length hm, by
      rw [word_truncate]
      exact List.prefix_iff_eq_take.mp hst⟩
  root_mem := by
    obtain ⟨s,hs⟩ := (C.level_evaluation_bijective 0 0 (by omega)).surjective
      ⟨(C.tree 0).root,rfl⟩
    exact ⟨0,s,by simp [word]⟩
  successor := by
    rintro s ⟨n,v,rfl⟩
    obtain ⟨w,hw⟩ := C.stableLevel_successor v
    have htake : (C.word w).take n = C.word v := by rw [← C.word_truncate w n (Nat.le_succ n),hw]
    have hn : n < (C.word w).length := by simp
    refine ⟨(C.word w)[n], n+1,w, ?_⟩
    rw [← htake, ← List.take_succ_eq_append_getElem hn]
    exact List.take_of_length_le (by simp)

end ControlledTower
end GameTree
end PolishSpaceBook.TreeGames
