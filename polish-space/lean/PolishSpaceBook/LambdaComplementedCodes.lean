module

public import PolishSpaceBook.LambdaIndexedOperations

@[expose] public section

/-! # Complemented codes with lambda-computed positive and negative indices

Validity is disjointness, not termination of an arbitrary input program.
Invalidity has a joint analytic witness at the original fixed parameter.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance complementedListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance complementedPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

def ValidComplementedIndex (ε : ℕ → ℕ) (n : ℕ) : Prop :=
  Disjoint (indexedProjection ε n.unpair.1) (indexedProjection ε n.unpair.2)

structure ComplementedCodes (ε : ℕ → ℕ) where
  positive : ℕ → ℕ
  negative : ℕ → ℕ
  positive_computable : ∃ F, NumericalComputes F positive
  negative_computable : ∃ F, NumericalComputes F negative
  separates : ∀ e f, Disjoint (indexedProjection ε e) (indexedProjection ε f) →
    indexedProjection ε e ⊆ indexedProjection ε (positive (Nat.pair e f)) ∧
    indexedProjection ε (positive (Nat.pair e f)) ⊆ (indexedProjection ε f)ᶜ ∧
    indexedProjection ε (positive (Nat.pair e f)) =
      (indexedProjection ε (negative (Nat.pair e f)))ᶜ

theorem exists_complementedCodes (ε : ℕ → ℕ) : Nonempty (ComplementedCodes ε) := by
  obtain ⟨p,n,hp,hn,h⟩ := exists_separationIndices ε
  exact ⟨⟨p,n,hp,hn,h⟩⟩

namespace ComplementedCodes
variable {ε : ℕ → ℕ} (C : ComplementedCodes ε)

def positiveSet (n : ℕ) : Set (ℕ → ℕ) := indexedProjection ε (C.positive n)
def negativeSet (n : ℕ) : Set (ℕ → ℕ) := indexedProjection ε (C.negative n)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Write $A_e$ for the uniform pair-tree projections at the fixed parameter. Let $\sigma,\tau$ be the two total
    index transformations supplied by uniform separation. For every $e=\NatPair{i}{j}$, put
    $$\begin{aligned}
    C&:=\{\NatPair{i}{j}:A_i\cap A_j=\emptyset\},\\
    D_e&:=A_{\sigma(e)},\qquad D'_e:=A_{\tau(e)},\\
    V_e&:=D_e,\qquad W_e:=(D'_e)^{\complement}.
    \end{aligned}$$
    The input programs need not be total: the delayed tree presentation defines $A_e$ for every index.
    The trees presenting $D_e$ and $D'_e$ have joint deciders in $e$ and the finite node, obtained by
    computing $\sigma(e)$ or $\tau(e)$ before running the uniform indexed-tree decider.
-/
theorem positive_family_decidable : LambdaRelative.DecidablePredicate ε
    (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (indexedTree ε (C.positive z.1)).tree) := by
  obtain ⟨F,hF⟩ := C.positive_computable
  exact indexedTree_reindex_decidable ε hF

theorem negative_family_decidable : LambdaRelative.DecidablePredicate ε
    (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (indexedTree ε (C.negative z.1)).tree) := by
  obtain ⟨F,hF⟩ := C.negative_computable
  exact indexedTree_reindex_decidable ε hF

theorem complementary {n : ℕ} (hn : ValidComplementedIndex ε n) :
    C.positiveSet n = (C.negativeSet n)ᶜ := by
  simpa only [Nat.pair_unpair,positiveSet,negativeSet] using
    (C.separates n.unpair.1 n.unpair.2 hn).2.2

theorem sound {n : ℕ} (hn : ValidComplementedIndex ε n) :
    Complemented ε (C.positiveSet n) := by
  refine ⟨⟨indexedTree ε (C.positive n),rfl⟩,?_⟩
  have he : (C.positiveSet n)ᶜ = C.negativeSet n := by rw [C.complementary hn,compl_compl]
  rw [he]
  exact ⟨indexedTree ε (C.negative n),rfl⟩

/-- The two separation inclusions force exact equality with the input set. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Uniformity follows from the joint tree deciders. If $e\in C$, separation gives
    $D_e=(D'_e)^{\complement}$, so $V_e=W_e$ and both sides of $V_e$ have the required presentations.
    Conversely, given such a set $A$, choose indices with $A_i=A$ and $A_j=A^{\complement}$.
    Then $e=\NatPair{i}{j}$ is valid, and the separation inclusions give
    $$A\IncludedIn D_e\IncludedIn(A^{\complement})^{\complement}=A.$$
    Hence $D_e=A$. This is an existence assertion for codes of a given set, not a procedure selecting codes
    from unspecified set data.
    \end{proof}
-/
theorem complete {A : Set (ℕ → ℕ)} (hA : Complemented ε A) :
    ∃ n, ValidComplementedIndex ε n ∧ C.positiveSet n = A := by
  obtain ⟨e,he⟩ := (projected_iff_index ε A).mp hA.1
  obtain ⟨f,hf⟩ := (projected_iff_index ε Aᶜ).mp hA.2
  have hd : Disjoint (indexedProjection ε e) (indexedProjection ε f) := by
    rw [← he,← hf]
    exact disjoint_compl_right
  refine ⟨Nat.pair e f,by simpa [ValidComplementedIndex] using hd,?_⟩
  have h := C.separates e f hd
  apply Subset.antisymm
  · simpa only [positiveSet,← hf,compl_compl] using h.2.1
  · simpa only [positiveSet,← he] using h.1

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Codes for sets and their complements
-/
theorem complemented_iff {A : Set (ℕ → ℕ)} :
    Complemented ε A ↔ ∃ n, ValidComplementedIndex ε n ∧ C.positiveSet n = A := by
  constructor
  · exact C.complete
  · rintro ⟨n,hn,rfl⟩
    exact C.sound hn

end ComplementedCodes

/-- Forget the old point, leaving a constant projection on the new point. -/
def PairTree.nonemptiness {ε : ℕ → ℕ} (T : PairTree ε) : PairTree ε :=
  (T.coordinatePreimage (projection_computes true)).projectRight

theorem pairTreeBody_nonemptiness {ε : ℕ → ℕ} (T : PairTree ε) (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody T.nonemptiness.tree ↔
      (leftBaire q,rightBaire q) ∈ pairTreeBody T.tree := by
  rw [PairTree.nonemptiness,pairTreeBody_projectRight,pairTreeBody_coordinatePreimage]
  simp only [Set.mem_preimage,Function.comp_def,pairBaire,Nat.unpair_pair,ite_true]

theorem pairTreeProjection_nonemptiness {ε : ℕ → ℕ} (T : PairTree ε) :
    pairTreeProjection T.nonemptiness.tree =
      {_x : ℕ → ℕ | (pairTreeProjection T.tree).Nonempty} := by
  rw [PairTree.nonemptiness,pairTreeProjection_projectRight,pairTreeProjection_coordinatePreimage]
  ext x
  constructor
  · rintro ⟨p,hp,_⟩
    exact ⟨leftBaire p,hp⟩
  · rintro ⟨y,hy⟩
    refine ⟨pairBaire y x,?_,rightBaire_pair y x⟩
    simpa only [mem_ofPred_eq,mem_preimage,pairBaire,Nat.unpair_pair,Function.comp_def,ite_true] using hy

theorem nonemptiness_family_decidable {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).nonemptiness.tree) :=
  projectRight_family_decidable (fun i => (T i).coordinatePreimage (projection_computes true))
    (coordinatePreimage_family_decidable T hT (projection_computes true))

def invalidComplementedTree (ε : ℕ → ℕ) (n : ℕ) : PairTree ε :=
  ((indexedTree ε n.unpair.1).intersection (indexedTree ε n.unpair.2)).nonemptiness

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For any pair tree $T$, first take the inverse image of its projection under the first coordinate of a
    coded pair, then project to the second coordinate. The resulting tree $N(T)$ has the exact body identity
    $$[N(T)]=\{(z,q):(\NameProjection{1}{q},\NameProjection{2}{q})\in[T]\}.$$
    Its projection is therefore the whole space when $\pi_0([T])$ is nonempty, and empty otherwise.
    The new point $z$ is unused; the witness stores the omitted point and the old witness. The word
    transformations and finite tests in these two operations preserve joint decidability in a family index.

    For $e=\NatPair{p}{q}$, take the intersection tree for $A_p\cap A_q$ and apply $N$ to it.
    A witness in $U_e$ stores a point $x$ and two witnesses for $x\in A_p$ and $x\in A_q$, as
    $\NamePair{x}{\NamePair{r}{t}}$. Conversely, such a point and two witnesses give a branch over every $z$.
    This proves the displayed projection identity, including empty input trees. Computing the projections of
    $e$, pairing witnesses, and retaining $e$ through the word operations gives one joint tree decider.
    Specializing it gives the claimed numerical index transformation. The whole-space/empty-space description
    is a statement about the projection; it is not a test deciding which case holds.
    \end{proof}
-/
theorem pairTreeBody_invalidComplementedTree (ε : ℕ → ℕ) (n : ℕ) (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody (invalidComplementedTree ε n).tree ↔
      (leftBaire q,leftBaire (rightBaire q)) ∈ pairTreeBody (indexedTree ε n.unpair.1).tree ∧
      (leftBaire q,rightBaire (rightBaire q)) ∈ pairTreeBody (indexedTree ε n.unpair.2).tree := by
  rw [invalidComplementedTree,pairTreeBody_nonemptiness,pairTreeBody_intersection]

theorem invalidComplementedTree_family_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (invalidComplementedTree ε z.1).tree) :=
  nonemptiness_family_decidable
    (fun n => (indexedTree ε n.unpair.1).intersection (indexedTree ε n.unpair.2))
    (intersection_family_decidable
      (fun n => indexedTree ε n.unpair.1) (fun n => indexedTree ε n.unpair.2)
      (indexedTree_reindex_decidable ε (computes_codeFirst numericalIdentity_computes))
      (indexedTree_reindex_decidable ε (computes_codeSecond numericalIdentity_computes)))

theorem pairTreeProjection_invalidComplementedTree (ε : ℕ → ℕ) (n : ℕ) :
    pairTreeProjection (invalidComplementedTree ε n).tree =
      {_x : ℕ → ℕ | ¬ ValidComplementedIndex ε n} := by
  rw [invalidComplementedTree,pairTreeProjection_nonemptiness,pairTreeProjection_intersection]
  ext _x
  simp only [mem_ofPred_eq,ValidComplementedIndex,indexedProjection]
  exact Set.not_disjoint_iff_nonempty_inter.symm

/-- Invalidity is represented uniformly, without deciding validity. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Uniform witnesses to invalid codes
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For any pair tree $T$, first take the inverse image of its projection under the first coordinate of a
    coded pair, then project to the second coordinate. The resulting tree $N(T)$ has the exact body identity
    $$[N(T)]=\{(z,q):(\NameProjection{1}{q},\NameProjection{2}{q})\in[T]\}.$$
    Its projection is therefore the whole space when $\pi_0([T])$ is nonempty, and empty otherwise.
    The new point $z$ is unused; the witness stores the omitted point and the old witness. The word
    transformations and finite tests in these two operations preserve joint decidability in a family index.

    For $e=\NatPair{p}{q}$, take the intersection tree for $A_p\cap A_q$ and apply $N$ to it.
    A witness in $U_e$ stores a point $x$ and two witnesses for $x\in A_p$ and $x\in A_q$, as
    $\NamePair{x}{\NamePair{r}{t}}$. Conversely, such a point and two witnesses give a branch over every $z$.
    This proves the displayed projection identity, including empty input trees. Computing the projections of
    $e$, pairing witnesses, and retaining $e$ through the word operations gives one joint tree decider.
    Specializing it gives the claimed numerical index transformation. The whole-space/empty-space description
    is a statement about the projection; it is not a test deciding which case holds.
    \end{proof}
-/
theorem exists_invalidComplementedIndices (ε : ℕ → ℕ) :
    ∃ invalid : ℕ → ℕ, (∃ F, NumericalComputes F invalid) ∧ ∀ n,
      indexedProjection ε (invalid n) = {_x : ℕ → ℕ | ¬ ValidComplementedIndex ε n} := by
  obtain ⟨invalid,hi,hc⟩ := treeFamily_indices ε (invalidComplementedTree ε)
    (invalidComplementedTree_family_decidable ε)
  refine ⟨invalid,hi,fun n => ?_⟩
  change pairTreeProjection (indexedTree ε (invalid n)).tree = _
  rw [pairTreeProjection_indexedTree ε (invalid n) _ (hc n),pairTreeProjection_invalidComplementedTree]

end LambdaTree
end PolishSpaceBook
