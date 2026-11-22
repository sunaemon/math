module

public import PolishSpaceBook.GameTreeInverseLevels

@[expose] public section

/-! # Branch projections of a controlled covering tower

A limit move records its component at every stage. Its alphabet is discrete,
not the product topology on that alphabet. The branch space still has the
usual product topology of moves. Coordinate projections realize exactly the
finite-composite projections of the stabilized prefixes.
-/
noncomputable section
namespace PolishSpaceBook.TreeGames.GameTree.ControlledTower
open Set Function
universe u
variable {A : ℕ → Type u} [∀ i, TopologicalSpace (A i)] {k : ℕ}
variable (C : ControlledTower A k)

/-- Every legal word has its coherent-level witness at its own length. -/
theorem limitNodes_level (s : List (∀ i, A i)) (hs : s ∈ C.limitNodes) :
    ∃ t : C.StableLevel s.length, s = C.word t := by
  obtain ⟨n,t,ht⟩ := hs
  have hn : n = s.length := by simpa only [C.word_length] using (congrArg List.length ht).symm
  subst n
  exact ⟨t,ht⟩

/-- The word retains every component of its coherent level. -/
theorem word_injective (n : ℕ) : Function.Injective (C.word (n := n)) := by
  intro s t h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Subtype.ext
  simpa only [C.word_component] using congrArg (List.map (fun a => a i)) h

/-- Each branch prefix determines a coherent level at exactly its length. -/
theorem exists_playLevel (x : C.limitTree.Play) (n : ℕ) :
    ∃ t : C.StableLevel n, seqPrefix x.val n = C.word t := by
  obtain ⟨m,t,ht⟩ := x.property n
  have hm : m = n := by simpa only [seqPrefix_length,C.word_length] using (congrArg List.length ht).symm
  subst m
  exact ⟨t,ht⟩

/-- Choose the unique coherent level represented by an initial segment of a limit play. -/
def playLevel (x : C.limitTree.Play) (n : ℕ) : C.StableLevel n :=
  (C.exists_playLevel x n).choose

theorem playLevel_spec (x : C.limitTree.Play) (n : ℕ) :
    seqPrefix x.val n = C.word (C.playLevel x n) := (C.exists_playLevel x n).choose_spec

/-- The stage-i prefix is the stage-i component of the stable level. -/
theorem component_prefix (x : C.limitTree.Play) (i n : ℕ) :
    seqPrefix (fun m => x.val m i) n = ((C.playLevel x n).val i).val.val := by
  have he := congrArg (List.map (fun a => a i)) (C.playLevel_spec x n)
  simpa only [C.word_component,seqPrefix,List.map_ofFn,Function.comp_def] using he

/-- Read the compatible stage-i branch coordinate by coordinate. -/
def project (x : C.limitTree.Play) (i : ℕ) : (C.tree i).Play :=
  ⟨fun n => x.val n i,fun n => by
    rw [C.component_prefix]
    exact ((C.playLevel x n).val i).val.property⟩

theorem project_prefixLevel (x : C.limitTree.Play) (i n : ℕ) :
    (C.tree i).prefixLevel (C.project x i) n = (C.playLevel x n).val i := by
  apply Subtype.ext
  apply Subtype.ext
  exact C.component_prefix x i n

/-- Bonding maps commute with the projections out of the limit tree. -/
theorem project_commutes (x : C.limitTree.Play) (i : ℕ) :
    (C.covering i).project (C.project x (i+1)) = C.project x i := by
  have he (n : ℕ) : (C.tree i).prefixLevel
      ((C.covering i).project (C.project x (i+1))) n =
      (C.tree i).prefixLevel (C.project x i) n := by
    rw [(C.covering i).prefix_project,C.project_prefixLevel,C.project_prefixLevel]
    exact (C.playLevel x n).property i
  apply Subtype.ext
  funext n
  have hp := congrArg (fun s => s.val.val[n]?) (he (n+1))
  simpa only [GameTree.prefixLevel,GameTree.prefixPosition,seqPrefix,
    List.getElem?_ofFn,show n < n+1 from Nat.lt_succ_self n, dite_eq_left trivial,Option.some.injEq] using hp

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For a branch $x\in[T_\infty]$, define $\rho_i(x)$ by projecting through the finite composite
    $$T_j\to T_{j-1}\to\cdots\to T_i$$
    on each prefix, where $j$ is chosen so large that the prefix has length $<k+j$. The coherence of the finite composites
    makes these prefix definitions compatible, hence determines a branch of $T_i$.
-/
/-- A stable prefix projected through any finite composite gives the same lower prefix. -/
theorem project_finite (x : C.limitTree.Play) (n j i : ℕ) (hi : i ≤ j) :
    (C.levels n).down j ((C.tree j).prefixLevel (C.project x j) n) i hi =
      (C.tree i).prefixLevel (C.project x i) n := by
  rw [C.project_prefixLevel,C.project_prefixLevel]
  exact (C.levels n).down_eq (C.playLevel x n) j i hi


/-- Each legal limit node represents one stable level of its own length. -/
theorem exists_nodeLevel {n : ℕ} (s : C.limitTree.Level n) :
    ∃ t : C.StableLevel n, s.val.val = C.word t := by
  obtain ⟨m,t,ht⟩ := s.val.property
  have hm : m = n := by simpa only [s.property,C.word_length] using (congrArg List.length ht).symm
  subst m
  exact ⟨t,ht⟩

def nodeLevel {n : ℕ} (s : C.limitTree.Level n) : C.StableLevel n :=
  (C.exists_nodeLevel s).choose

theorem nodeLevel_spec {n : ℕ} (s : C.limitTree.Level n) :
    s.val.val = C.word (C.nodeLevel s) := (C.exists_nodeLevel s).choose_spec

def levelNode {n : ℕ} (s : C.StableLevel n) : C.limitTree.Level n :=
  ⟨⟨C.word s,⟨n,s,rfl⟩⟩,C.word_length s⟩

/-- The literal finite words and the coherent stabilized levels are equivalent. -/
def nodeEquiv (n : ℕ) : C.limitTree.Level n ≃ C.StableLevel n where
  toFun := C.nodeLevel
  invFun := C.levelNode
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact (C.nodeLevel_spec s).symm
  right_inv s := by
    apply C.word_injective n
    exact (C.nodeLevel_spec (C.levelNode s)).symm

/-- The limit prefix map is evaluation of the coherent level at stage i. -/
def limitNodeMap (i n : ℕ) (s : C.limitTree.Level n) : (C.tree i).Level n :=
  (C.nodeEquiv n s).val i

theorem limitNodeMap_prefix (x : C.limitTree.Play) (i n : ℕ) :
    (C.tree i).prefixLevel (C.project x i) n = C.limitNodeMap i n (C.limitTree.prefixLevel x n) := by
  have he : C.nodeLevel (C.limitTree.prefixLevel x n) = C.playLevel x n := by
    apply C.word_injective n
    rw [← C.nodeLevel_spec, ← C.playLevel_spec]
    rfl
  rw [C.project_prefixLevel]
  exact congrArg (fun s : C.StableLevel n => s.val i) he.symm

/-- Every projection is bijective through its controlled opening k+i. -/
theorem limitNodeMap_bijective (i n : ℕ) (hn : n ≤ k+i) :
    Function.Bijective (C.limitNodeMap i n) :=
  (C.level_evaluation_bijective n i hn).comp (C.nodeEquiv n).bijective

/-- All simultaneous-stage moves are treated as discrete auxiliary moves. -/
@[reducible] def limitMoveTopology : TopologicalSpace (∀ i, A i) := ⊥

/-- Every finite output coordinate reads just the matching limit move. -/
theorem project_continuous (i : ℕ) :
    letI : TopologicalSpace (∀ i, A i) := limitMoveTopology
    Continuous (fun x : C.limitTree.Play => C.project x i) := by
  let : TopologicalSpace (∀ i, A i) := limitMoveTopology
  let : DiscreteTopology (∀ i, A i) := ⟨rfl⟩
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := fun a : ∀ i, A i => a i)).comp
    ((continuous_apply n).comp continuous_subtype_val)

end PolishSpaceBook.TreeGames.GameTree.ControlledTower
