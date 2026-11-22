module

public import PolishSpaceBook.LambdaTreeMapFiniteTests
public import PolishSpaceBook.WellFoundedRankBounds

@[expose] public section

/-! # A concrete rank bound from disjoint pair-tree projections

The joint tree searches for one point and witnesses in both trees. A witness
on the first side embeds the second section into the joint tree. Disjointness
makes this single, countable bound well founded. No ordinal notation is chosen.
-/
namespace PolishSpaceBook
open Set NamedLambda

namespace RootedPrefixTree

/-- The strict-extension relation on all numerical word codes; invalid words
are isolated. -/
def codedExtension (T : RootedPrefixTree) (b a : ℕ) : Prop :=
  NatListCode.decode b ∈ T.tree ∧ NatListCode.decode a ∈ T.tree ∧
    prefixOf (NatListCode.decode a) (NatListCode.decode b) ∧
    (NatListCode.decode a).length < (NatListCode.decode b).length

theorem codedExtension_wellFounded (T : RootedPrefixTree)
    (hT : WellFounded (strictTreeExtension T.tree)) : WellFounded T.codedExtension := by
  classical
  let f : ℕ → T.tree := fun n =>
    if h : NatListCode.decode n ∈ T.tree then ⟨NatListCode.decode n,h⟩ else T.root
  apply wellFounded_of_relation_preserving hT f
  intro b a h
  simpa only [f,dite_eq_left h.1,dite_eq_left h.2.1,strictTreeExtension] using h.2.2

theorem codedExtension_wellFounded_of_root_acc (T : RootedPrefixTree)
    (h : Acc T.codedExtension 0) : WellFounded T.codedExtension := by
  constructor
  intro a
  by_cases ha : NatListCode.decode a ∈ T.tree
  · by_cases he : NatListCode.decode a = []
    · have hz : a = 0 := by
        have := congrArg NatListCode.encode he
        simpa [NatListCode.encode_decode,NatListCode.encode] using this
      simpa [hz] using h
    · apply h.inv
      exact ⟨ha,by simpa [NatListCode.decode] using T.root_mem,
        by simp [NatListCode.decode,prefixOf],by simpa [NatListCode.decode] using List.length_pos_iff.mpr he⟩
  · constructor
    intro b hb
    exact False.elim (ha hb.2.1)

theorem wellFounded_of_codedExtension (T : RootedPrefixTree)
    (hT : WellFounded T.codedExtension) : WellFounded (strictTreeExtension T.tree) := by
  apply wellFounded_of_relation_preserving hT (fun s : T.tree => NatListCode.encode s.val)
  intro b a h
  simpa only [codedExtension,NatListCode.decode_encode] using
    (show b.val ∈ T.tree ∧ a.val ∈ T.tree ∧ prefixOf a.val b.val ∧ a.val.length < b.val.length from
      ⟨b.property,a.property,h⟩)

end RootedPrefixTree

namespace RankBound

theorem holds_of_relation_preserving {α β : Type} (R : β → β → Prop) (hR : WellFounded R)
    (E : α → α → Prop) (f : α → β) (hf : ∀ ⦃t s⦄, E t s → R (f t) (f s)) (s : α) :
    Holds R hR E (f s) s := by
  have hE := wellFounded_of_relation_preserving hR f hf
  let : WellFounded E := hE
  let : WellFounded R := hR
  exact ⟨hE.apply s,wellFoundedRank_le_of_relation_preserving f hf s⟩

end RankBound

namespace LambdaTree

/-- Flatten the point and witness coordinates into a single word, retaining
an empty root even if the original pair tree has none. -/
def flattenedTree {ε : ℕ → ℕ} (D : PairTree ε) : RootedPrefixTree where
  tree := {w | w = [] ∨ (leftWitness w,rightWitness w) ∈ D.tree}
  root_mem := Or.inl rfl
  downward := by
    intro s t ht hst
    rcases ht with rfl | ht
    · exact Or.inl (List.prefix_nil.mp hst)
    · right
      have h := D.downward _ ht s.length
      have he := List.prefix_iff_eq_take.mp hst
      simpa only [← List.map_take,leftWitness,rightWitness,← he] using h

theorem treeBody_flattenedTree {ε : ℕ → ℕ} (D : PairTree ε) (q : ℕ → ℕ) :
    q ∈ treeBody (flattenedTree D).tree ↔ (leftBaire q,rightBaire q) ∈ pairTreeBody D.tree := by
  constructor
  · intro h n
    have hn := h (n+1)
    change seqPrefix q (n+1) = [] ∨ _ at hn
    have hne : seqPrefix q (n+1) ≠ [] := by
      intro he
      have := congrArg List.length he
      simp [seqPrefix_length] at this
    have hm := D.downward _ (hn.resolve_left hne) n
    simpa only [leftWitness_prefix,rightWitness_prefix,seqPrefix_take_of_le _ (Nat.le_succ n)] using hm
  · intro h n
    right
    simpa only [leftWitness_prefix,rightWitness_prefix] using h n

def jointTree {ε : ℕ → ℕ} (T S : PairTree ε) : RootedPrefixTree :=
  flattenedTree (T.intersection S)

theorem jointTree_wellFounded {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    WellFounded (strictTreeExtension (jointTree T S).tree) := by
  apply (prefixTreeWellFounded_iff _ (jointTree T S).downward).mp
  rintro ⟨q,hq⟩
  have hb := (treeBody_flattenedTree (T.intersection S) q).mp hq
  have hm : leftBaire q ∈ pairTreeProjection (T.intersection S).tree := ⟨rightBaire q,hb⟩
  rw [pairTreeProjection_intersection] at hm
  exact Set.disjoint_left.mp hd hm.1 hm.2

/-- With the point and first witness fixed, insert a word in the second
witness coordinate. This is a semantic rank comparison, not a computation of
a witness from membership in a projection. -/
def jointWord (x p : ℕ → ℕ) (w : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin w.length => Nat.pair (x i) (Nat.pair (p i) w[i]))

@[simp] theorem jointWord_length (x p : ℕ → ℕ) (w : List ℕ) :
    (jointWord x p w).length = w.length := by simp [jointWord]

@[simp] theorem jointWord_nil (x p : ℕ → ℕ) : jointWord x p [] = [] := by simp [jointWord]

@[simp] theorem leftWitness_jointWord (x p : ℕ → ℕ) (w : List ℕ) :
    leftWitness (jointWord x p w) = seqPrefix x w.length := by
  simp [jointWord,leftWitness,seqPrefix,List.map_ofFn,Function.comp_def]

@[simp] theorem leftRight_jointWord (x p : ℕ → ℕ) (w : List ℕ) :
    leftWitness (rightWitness (jointWord x p w)) = seqPrefix p w.length := by
  simp [jointWord,leftWitness,rightWitness,seqPrefix,List.map_ofFn,Function.comp_def]

@[simp] theorem rightRight_jointWord (x p : ℕ → ℕ) (w : List ℕ) :
    rightWitness (rightWitness (jointWord x p w)) = w := by
  simp [jointWord,rightWitness,List.map_ofFn,Function.comp_def]

theorem jointWord_prefix (x p : ℕ → ℕ) {u v : List ℕ} (h : prefixOf u v) :
    prefixOf (jointWord x p u) (jointWord x p v) := by
  apply List.prefix_iff_eq_take.mpr
  apply List.ext_getElem
  · simp [jointWord_length,List.length_take,Nat.min_eq_left h.length_le]
  · intro i hi hj
    have hiu : i < u.length := by simpa using hi
    simp only [jointWord,List.getElem_ofFn,List.getElem_take]
    congr 2
    exact h.getElem hiu

theorem jointWord_mem {ε : ℕ → ℕ} (T S : PairTree ε) (x p : ℕ → ℕ)
    (hp : (x,p) ∈ pairTreeBody T.tree) (w : List ℕ) (hw : w ∈ (rootedSection S x).tree) :
    jointWord x p w ∈ (jointTree T S).tree := by
  rcases hw with rfl | hw
  · left; exact jointWord_nil x p
  · right
    change (leftWitness _,leftWitness (rightWitness _)) ∈ T.tree ∧
      (leftWitness _,rightWitness (rightWitness _)) ∈ S.tree
    simpa only [leftWitness_jointWord,leftRight_jointWord,rightRight_jointWord] using ⟨hp w.length,hw⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Joint-tree rank bound
  excerpt: |
    The tree $J$ is well founded. For every $x\in A$, the section $S_x$ is well founded and its root rank
    is at most the root rank of $J$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    An infinite branch through $J$ would give a point with witnesses in both $T$ and $S$, contradicting
    disjointness. Adding the empty root does not create a branch: membership at every positive length
    implies membership at length zero in the original pair trees by downward closure.
    For $x\in A$, fix a witness $p$ with $\Pair{x}{p}\in[T]$. Map a word $v\in S_x$ to
    $$\WordPair{\restrict{x}{\Length{v}}}{\WordPair{\restrict{p}{\Length{v}}}{v}}.$$
    This word belongs to $J$, has length $\Length{v}$, and the map sends the root to the root and preserves
    strict extension. The tree-rank comparison lemma proves the assertion. The witness $p$ is used only
    in this rank comparison; the membership program for $J$ does not select such a witness.
-/
theorem jointTree_rank_bound {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree))
    (x : ℕ → ℕ) (hx : x ∈ pairTreeProjection T.tree) :
    ∃ hS : WellFounded (strictTreeExtension (rootedSection S x).tree),
      (hS.apply (rootedSection S x).root).rank ≤
        ((jointTree_wellFounded T S hd).apply (jointTree T S).root).rank := by
  obtain ⟨p,hp⟩ := hx
  let f : (rootedSection S x).tree → (jointTree T S).tree := fun w =>
    ⟨jointWord x p w.val,jointWord_mem T S x p hp w.val w.property⟩
  have hf : ∀ ⦃u v⦄, strictTreeExtension (rootedSection S x).tree u v →
      strictTreeExtension (jointTree T S).tree (f u) (f v) := by
    intro u v h
    exact ⟨jointWord_prefix x p h.1,by simpa only [f,jointWord_length] using h.2⟩
  have hS := wellFounded_of_relation_preserving (jointTree_wellFounded T S hd) f hf
  let : WellFounded (strictTreeExtension (rootedSection S x).tree) := hS
  let : WellFounded (strictTreeExtension (jointTree T S).tree) :=
    jointTree_wellFounded T S hd
  have hroot : f (rootedSection S x).root = (jointTree T S).root := by
    apply Subtype.ext
    exact jointWord_nil x p
  refine ⟨hS,?_⟩
  have h := wellFoundedRank_le_of_relation_preserving f hf (rootedSection S x).root
  rw [hroot] at h
  exact h

theorem jointWord_preserves {ε : ℕ → ℕ} (T S : PairTree ε) (x p : ℕ → ℕ)
    (hp : (x,p) ∈ pairTreeBody T.tree) {b a : ℕ}
    (h : (rootedSection S x).codedExtension b a) :
    (jointTree T S).codedExtension (NatListCode.encode (jointWord x p (NatListCode.decode b)))
      (NatListCode.encode (jointWord x p (NatListCode.decode a))) := by
  simpa only [RootedPrefixTree.codedExtension,NatListCode.decode_encode,jointWord_length] using
    (show jointWord x p (NatListCode.decode b) ∈ (jointTree T S).tree ∧
      jointWord x p (NatListCode.decode a) ∈ (jointTree T S).tree ∧
      prefixOf (jointWord x p (NatListCode.decode a)) (jointWord x p (NatListCode.decode b)) ∧
      (NatListCode.decode a).length < (NatListCode.decode b).length from
      ⟨jointWord_mem T S x p hp _ h.1,jointWord_mem T S x p hp _ h.2.1,
        jointWord_prefix x p h.2.2.1,h.2.2.2⟩)

theorem jointRank_separates {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    let J := jointTree T S
    let hJ := J.codedExtension_wellFounded (jointTree_wellFounded T S hd)
    pairTreeProjection T.tree ⊆ {x | RankBound.Holds J.codedExtension hJ
      (rootedSection S x).codedExtension 0 0} ∧
    {x | RankBound.Holds J.codedExtension hJ (rootedSection S x).codedExtension 0 0}
      ⊆ (pairTreeProjection S.tree)ᶜ := by
  dsimp only
  constructor
  · rintro x ⟨p,hp⟩
    have h := RankBound.holds_of_relation_preserving _
      ((jointTree T S).codedExtension_wellFounded (jointTree_wellFounded T S hd))
      (rootedSection S x).codedExtension
      (fun n => NatListCode.encode (jointWord x p (NatListCode.decode n)))
      (fun {_ _} h => jointWord_preserves T S x p hp h) 0
    simpa only [Set.mem_ofPred_eq,NatListCode.decode,jointWord_nil,NatListCode.encode] using h
  · rintro x ⟨hacc,hbound⟩ hx
    have hw := (rootedSection S x).wellFounded_of_codedExtension
      ((rootedSection S x).codedExtension_wellFounded_of_root_acc hacc)
    exact (prefixTreeWellFounded_iff _ (rootedSection S x).downward).mpr hw
      ((branch_rootedSection_iff S x).mpr hx)

end LambdaTree
end PolishSpaceBook
