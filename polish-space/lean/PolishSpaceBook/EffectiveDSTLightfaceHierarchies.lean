module

public import PolishSpaceBook.LambdaKleeneNotations
public import PolishSpaceBook.CantorBaireSpace
public import PolishSpaceBook.AnalyticSetsSuslinSchemes

@[expose] public section

/-!
# Effective descriptive set theory: lightface hierarchies

Formalization targets for `polish-space/src/polish-space-book/effective-dst-lightface-hierarchies.md`.

This file formalizes the set-theoretic core used by the chapter: the finite
stage-cutoff tree attached to an enumeration of forbidden cylinders, pair-tree
sections and projections, and the two diagonal contradictions.  The repository
adds lambda-decidable membership in `LambdaRecursiveTrees.lean` and the
lambda closed-set representation in `EffectiveClosedTreeRepresentation.lean`.
`LambdaRelativeEnumerations.lean` supplies total enumeration by finite
acceptance tests. The ordinary `RecursivePrefixTree` now uses this lambda API.
`LambdaPairTrees` adds relative pair-tree presentations and their finite
closure operations. `LambdaRelativePredicates` supplies fixed-parameter
lambda decision, Boolean closure, countability from syntax indices, and a
common real parameter. `LambdaArithmeticNormalForm` supplies the formula
normal forms, while `LambdaRelativeJump` gives relative diagonal halting,
its exact semidecider, the complement obstruction, and recovery of the old
set from its jump by a computed index map. `LambdaRecursiveOrdinals`
constructs initial segments and successors of lambda-decidable numerical
well orders and proves the countable least-nonrecursive boundary.
`LambdaPureParameters` eliminates computable input parameters by beta
substitution. `KleeneBrouwerOrder` proves well-foundedness by least occupied
children, and `LambdaKleeneBrouwer` supplies a pure comparison term and a
recursive ordinal bound for every node of a relative recursive well-founded
tree. `LambdaKleeneNotations` constructs the least simultaneous notation
system and proves its well-foundedness and unique countable ordinal
interpretation. `LambdaIteratedJump` constructs the unique set-valued jump
hierarchy for each starting set, supplies the lambda row reader for limits,
and proves strict increase along notation precedence. `LambdaNotationCoverage`
constructs upper notations from recursive well orders and proves that every
recursive ordinal has a notation. `LambdaNotationBounds` proves the converse
using certified descent trees and recursive Kleene--Brouwer bounds. The
witness-table construction in `LambdaJumpTables`, its arithmetic matrix in
`LambdaJumpTableMatrix`, and `LambdaHyperarithmeticInclusion` prove that sets
computed from iterated jumps are lightface ambiguous. The converse
hyperarithmetic characterization remains open.
Claims requiring that infrastructure, together with the
cited Kleene-tree and Spector-uniqueness theorems, are marked explicitly in
the source.
-/

namespace PolishSpaceBook

open Set

section ClosedTreeCoding

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    A tree is closed under initial segments, so $t\in T$ and $s\prefixOf t$ imply $s\in T$.
-/
theorem subtree_mem_of_prefix {T : Set (finseq ℕ)} (hT : IsSubtree T)
    {s t : finseq ℕ} (ht : t ∈ T) (hst : prefixOf s t) :
    s ∈ T :=
  hT ht hst

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Its body
    $$
    [T]:=\{p\in\BaireSpace:\restrict{p}{n}\in T\text{ for all }n\}
    $$
    records its infinite branches.
-/
theorem mem_effectiveDst_treeBody {T : Set (finseq ℕ)} {p : ℕ → ℕ} :
    p ∈ treeBody T ↔ ∀ n, seqPrefix p n ∈ T :=
  Iff.rfl

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: lemma
  title: Stage-cutoff tree identity
-/
/-- The finite-stage cutoff tree associated with an enumeration of forbidden
finite words.  No computability structure is needed for its set-theoretic
definition. -/
def stageCutoffTree (forbidden : ℕ → finseq ℕ) : Set (finseq ℕ) :=
  {t | ∀ i, i ≤ t.length → ¬ prefixOf (forbidden i) t}

theorem stageCutoffTree_isSubtree (forbidden : ℕ → finseq ℕ) :
    IsSubtree (stageCutoffTree forbidden) := by
  intro s t ht hst i hi hbad
  exact ht i (hi.trans hst.length_le) (hbad.trans hst)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The definition is downward closed: if $u\prefixOf t$ and $s_i\prefixOf u$ with $i\le|u|$, then $s_i\prefixOf t$ and
    $i\le|t|$. If $s_i\prefixOf p$, then $\restrict{p}{n}\notin T$ once $n\ge\max\{i,|s_i|\}$. Conversely, if
    $\restrict{p}{n}\notin T$, some $s_i$ with $i\le n$ is a prefix of $\restrict{p}{n}$ and hence of $p$. These two
    implications give the displayed identity.
    \end{proof}
-/
/-- The body of the stage-cutoff tree is exactly the complement of the union
of the enumerated forbidden cylinders. -/
theorem treeBody_stageCutoffTree (forbidden : ℕ → finseq ℕ) :
    treeBody (stageCutoffTree forbidden) = (⋃ i, cyl (forbidden i))ᶜ := by
  ext p
  constructor
  · intro hp
    change p ∉ ⋃ i, cyl (forbidden i)
    intro hUnion
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hUnion
    let n := max i (forbidden i).length
    have hT := hp n
    have hi_n : i ≤ (seqPrefix p n).length := by
      rw [seqPrefix_length]
      exact Nat.le_max_left i (forbidden i).length
    have hnot : ¬ prefixOf (forbidden i) (seqPrefix p n) :=
      hT i hi_n
    have hshort :
        prefixOf (seqPrefix p (forbidden i).length) (seqPrefix p n) :=
      seqPrefix_prefixOf_of_le p (Nat.le_max_right _ _)
    have heq : seqPrefix p (forbidden i).length = forbidden i :=
      seqPrefix_eq_of_mem_cyl hi
    apply hnot
    simpa [heq] using hshort
  · intro hp n
    change ∀ i, i ≤ (seqPrefix p n).length →
      ¬ prefixOf (forbidden i) (seqPrefix p n)
    intro i _hi hprefix
    apply hp
    exact Set.mem_iUnion.mpr ⟨i,
      prefixOfSeq_of_prefix hprefix (prefixOfSeq_seqPrefix p n)⟩

end ClosedTreeCoding

section PairTrees

/-- Body of a tree on synchronized pairs of finite words. -/
def pairTreeBody (T : Set (finseq ℕ × finseq ℕ)) :
    Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  {pq | ∀ n, (seqPrefix pq.1 n, seqPrefix pq.2 n) ∈ T}

/-- Projection of a pair-tree body to its first infinite coordinate. -/
def pairTreeProjection (T : Set (finseq ℕ × finseq ℕ)) : Set (ℕ → ℕ) :=
  {p | ∃ q, (p, q) ∈ pairTreeBody T}

/-- Section tree obtained after fixing the first infinite coordinate. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Given a recursive tree $T$ on pairs, define for each $p$ the section tree
    $$
    T_p:=\{t\in\finseq{\omega}:(\restrict{p}{|t|},t)\in T\}.
    $$
-/
def pairSectionTree (T : Set (finseq ℕ × finseq ℕ)) (p : ℕ → ℕ) :
    Set (finseq ℕ) :=
  {t | (seqPrefix p t.length, t) ∈ T}

/-- For prefix trees, well-foundedness means absence of an infinite branch. -/
def PrefixTreeWellFounded (T : Set (finseq ℕ)) : Prop :=
  ¬ ∃ q : ℕ → ℕ, q ∈ treeBody T

theorem mem_pairTreeProjection_iff_has_section_branch
    (T : Set (finseq ℕ × finseq ℕ)) (p : ℕ → ℕ) :
    p ∈ pairTreeProjection T ↔
      ∃ q : ℕ → ℕ, q ∈ treeBody (pairSectionTree T p) := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    intro n
    change (seqPrefix p (seqPrefix q n).length, seqPrefix q n) ∈ T
    simpa [seqPrefix_length] using hq n
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    intro n
    have hn := hq n
    change (seqPrefix p (seqPrefix q n).length, seqPrefix q n) ∈ T at hn
    simpa [seqPrefix_length] using hn

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: lemma
  title: Pair-tree section test
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    A branch $q$ through $T_p$ is exactly a witness satisfying
    $(\restrict{p}{n},\restrict{q}{n})\in T$ for every $n$. Negating the existence of such a branch gives the equivalence.
    \end{proof}
-/
theorem not_mem_pairTreeProjection_iff_section_wellFounded
    (T : Set (finseq ℕ × finseq ℕ)) (p : ℕ → ℕ) :
    p ∉ pairTreeProjection T ↔ PrefixTreeWellFounded (pairSectionTree T p) := by
  constructor
  · intro hp hbranch
    exact hp ((mem_pairTreeProjection_iff_has_section_branch T p).2 hbranch)
  · intro hwell hp
    exact hwell ((mem_pairTreeProjection_iff_has_section_branch T p).1 hp)

end PairTrees

section DiagonalArguments

/-- Diagonal for a naturally indexed family of sets of Baire-space points,
using the first coordinate of a point as its index. -/
def firstCoordinateDiagonal (U : ℕ → Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {p | p ∉ U (p 0)}

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: lemma
  title: First-coordinate diagonal
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    If $D=U_e$, choose any $p$ with $p(0)=e$. Then
    $$p\in D\quad\Longleftrightarrow\quad p\notin U_e\quad\Longleftrightarrow\quad p\notin D,$$
    a contradiction.
    \end{proof}
-/
/-- The first-coordinate diagonal cannot be any indexed section. -/
theorem firstCoordinateDiagonal_ne_section
    (U : ℕ → Set (ℕ → ℕ)) (e : ℕ) :
    firstCoordinateDiagonal U ≠ U e := by
  intro h
  let p : ℕ → ℕ := fun _ ↦ e
  have hp := Set.ext_iff.mp h p
  simp [firstCoordinateDiagonal, p] at hp

/-- The usual self-diagonal for a family indexed by its own underlying type. -/
def selfDiagonal {I : Type*} (U : I → Set I) : Set I :=
  {a | a ∉ U a}

/-- The self-diagonal cannot be a section of the family. -/
theorem selfDiagonal_ne_section {I : Type*} (U : I → Set I) (a : I) :
    selfDiagonal U ≠ U a := by
  intro h
  have ha := Set.ext_iff.mp h a
  simp [selfDiagonal] at ha

end DiagonalArguments

end PolishSpaceBook
