module

public import PolishSpaceBook.LambdaCountableOperations
public import PolishSpaceBook.TreeMapWitnessGeometry

@[expose] public section

/-! # Finite comparison-map tests with the book's lambda list coding

Image words may be longer than the input words. Target membership is
therefore delayed until enough point coordinates are present.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance mapListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance mapPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Membership tested from a sufficiently long point prefix. -/
def finiteSectionNode (T : Set (finseq ℕ × finseq ℕ)) (s t : finseq ℕ) : Prop :=
  t = [] ∨ (s.take t.length, t) ∈ T

/-- The root is included even when the original section is empty. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here we give the programs used for effective separation. A pair tree is a downward-closed set of equal-length
    pairs of finite words. Its section at $x$ consists of the words $u$ with $(\restrict{x}{|u|},u)$ in the tree,
    with the empty word added. Suppose closed programs $P_T,P_S$ decide two families of pair trees at the same
    parameter, on input $\NatPair{i}{\NatPair{a}{b}}$, where $a,b$ are word codes. In this subsection,
    expand all abbreviations before abstraction and choose fresh binders. The symbol $Z$ denotes the numerical
    zero test returning one on zero and zero otherwise.
-/
def rootedSection {ε : ℕ → ℕ} (T : PairTree ε) (x : ℕ → ℕ) :
    RootedPrefixTree where
  tree := {t | t = [] ∨ (seqPrefix x t.length, t) ∈ T.tree}
  root_mem := Or.inl rfl
  downward := by
    intro s t ht hst
    rcases ht with rfl | ht
    · exact Or.inl (List.prefix_nil.mp hst)
    · right
      have h := T.downward _ ht s.length
      rw [seqPrefix_take_of_le x hst.length_le, ← List.prefix_iff_eq_take.mp hst] at h
      exact h

theorem finiteSectionNode_prefix {ε : ℕ → ℕ} (T : PairTree ε)
    (x : ℕ → ℕ) (t : finseq ℕ) (n : ℕ) (ht : t.length ≤ n) :
    finiteSectionNode T.tree (seqPrefix x n) t ↔ t ∈ (rootedSection T x).tree := by
  simp only [finiteSectionNode, seqPrefix_take_of_le x ht, rootedSection, Set.mem_ofPred_eq]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For the uniformity assertion we make the finite comparison tests explicit. If $T$ is a pair tree, put
    $$T_x:=\{u:u=[]\lor(\restrict{x}{|u|},u)\in T\}.$$
    Adding the empty root does not add a branch: membership at length $n+1$ in the original tree implies
    membership at length $n$ by downward closure. Thus $T_x$ has a branch exactly when $x\in\pi_0([T])$.
    Write $c(u)=\LambdaListCode{u}$, and let $u_i$ be the unique word with code $i$.
    For a finite word $t$, let $f_t(u)$ be the word coded by its entry $t_{c(u)}$, using code zero when that
    entry is absent. For an infinite sequence $q$, let $f_q(u)$ be the word coded by $q(c(u))$.
    Every map on finite words has this form for some $q$.
-/
theorem treeBody_rootedSection {ε : ℕ → ℕ} (T : PairTree ε)
    (x y : ℕ → ℕ) : y ∈ treeBody (rootedSection T x).tree ↔ (x, y) ∈ pairTreeBody T.tree := by
  constructor
  · intro hy n
    have h := hy (n + 1)
    change seqPrefix y (n + 1) = [] ∨ _ at h
    have hn : seqPrefix y (n + 1) ≠ [] := by
      intro he
      have := congrArg List.length he
      simp [seqPrefix_length] at this
    have hmem := h.resolve_left hn
    simp only [seqPrefix_length] at hmem
    have hc := T.downward _ hmem n
    simpa only [seqPrefix_take_of_le _ (Nat.le_succ n)] using hc
  · intro h n
    exact Or.inr (by simpa [seqPrefix_length] using h n)

theorem branch_rootedSection_iff {ε : ℕ → ℕ} (T : PairTree ε)
    (x : ℕ → ℕ) : (∃ y, y ∈ treeBody (rootedSection T x).tree) ↔
      x ∈ pairTreeProjection T.tree := by
  exact exists_congr fun y => treeBody_rootedSection T x y

def wordOfCode (n : ℕ) : finseq ℕ := NatListCode.decode n

@[simp] theorem wordOfCode_encode (t : finseq ℕ) : wordOfCode (NatListCode.encode t) = t :=
  NatListCode.decode_encode t

def codedWordMap (q : ℕ → ℕ) (t : finseq ℕ) : finseq ℕ :=
  wordOfCode (q (NatListCode.encode t))

theorem codedWordMap_surjective (f : finseq ℕ → finseq ℕ) :
    ∃ q, codedWordMap q = f := by
  refine ⟨fun n => NatListCode.encode (f (wordOfCode n)), ?_⟩
  funext t
  simp [codedWordMap]

theorem treeComparisonLe_iff_code (T S : RootedPrefixTree) :
    TreeComparisonLe T S ↔ ∃ q, codedWordMap q [] = [] ∧
      IsTreeMapWitness T S (codedWordMap q) := by
  constructor
  · rintro ⟨f, hf, hmap⟩
    obtain ⟨g, hg, heq⟩ := treeMapWitness_of_map T S f hmap
    obtain ⟨q, rfl⟩ := codedWordMap_surjective g
    refine ⟨q, ?_, hg⟩
    exact (heq T.root).trans (congrArg Subtype.val hf)
  · rintro ⟨q, hroot, hmap⟩
    refine ⟨fun t => ⟨codedWordMap q t.val, hmap.1 t.val t.property⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact hroot
    · intro u v h
      exact hmap.2 u.val u.property v.val h.1 h.2

theorem treeComparisonLt_iff_code (T S : RootedPrefixTree) :
    TreeComparisonLt T S ↔ ∃ q, codedWordMap q [] ≠ [] ∧
      IsTreeMapWitness T S (codedWordMap q) := by
  constructor
  · rintro ⟨f, hf, hmap⟩
    obtain ⟨g, hg, heq⟩ := treeMapWitness_of_map T S f hmap
    obtain ⟨q, rfl⟩ := codedWordMap_surjective g
    refine ⟨q, ?_, hg⟩
    exact fun h => hf ((heq T.root).symm.trans h)
  · rintro ⟨q, hroot, hmap⟩
    refine ⟨fun t => ⟨codedWordMap q t.val, hmap.1 t.val t.property⟩, hroot, ?_⟩
    intro u v h
    exact hmap.2 u.val u.property v.val h.1 h.2

def finiteWordMap (q t : finseq ℕ) : finseq ℕ :=
  wordOfCode ((q[NatListCode.encode t]?).getD 0)

theorem finiteWordMap_prefix (q : ℕ → ℕ) (t : finseq ℕ) (n : ℕ) (ht : NatListCode.encode t < n) :
    finiteWordMap (seqPrefix q n) t = codedWordMap q t := by
  simp [finiteWordMap, codedWordMap, seqPrefix, ht]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Define the finite section test by
    $$R_T(s,u)\quad\Longleftrightarrow\quad u=[]\lor(\restrict{s}{|u|},u)\in T.$$
    Fix a root condition $r$, either $r(u)\Longleftrightarrow u=[]$ or $r(u)\Longleftrightarrow u\ne[]$.
    At a pair $(s,t)$, with $n=|s|$, require $r(f_t([]))$ when $0<n$.
    For each $i<n$, put $u=u_i$. If $c(u)<n$, $|u|\le n$, and $R_T(s,u)$, require both
    $$|f_t(u)|\le n\quad\Longrightarrow\quad R_S(s,f_t(u))$$
    and, for every $j<n$ with $v=u_j$,
    $$\begin{gathered}
    c(v)<n,\quad v\prefixOf u,\quad |v|<|u|\\
    \Longrightarrow\quad f_t(v)\prefixOf f_t(u),\quad |f_t(v)|<|f_t(u)|.
    \end{gathered}$$
    Let $R_r(s,t)$ denote the conjunction of these requirements. The code guards are redundant inside the
    bounded loops but indicate exactly which entries of an infinite map are available on synchronized prefixes.
    The image-length guard is essential: membership in the target section must wait until the point prefix is long enough.
-/
def treeMapFiniteTest (T S : Set (finseq ℕ × finseq ℕ))
    (rootTest : finseq ℕ → Prop) (z : finseq ℕ × finseq ℕ) : Prop :=
  (NatListCode.encode ([] : finseq ℕ) < z.1.length → rootTest (finiteWordMap z.2 [])) ∧
  ∀ i < z.1.length, ∀ u : finseq ℕ, u = wordOfCode i →
    NatListCode.encode u < z.1.length → u.length ≤ z.1.length → finiteSectionNode T z.1 u →
      ((finiteWordMap z.2 u).length ≤ z.1.length →
        finiteSectionNode S z.1 (finiteWordMap z.2 u)) ∧
      ∀ j < z.1.length, ∀ v : finseq ℕ, v = wordOfCode j →
        NatListCode.encode v < z.1.length → prefixOf v u → v.length < u.length →
          prefixOf (finiteWordMap z.2 v) (finiteWordMap z.2 u) ∧
          (finiteWordMap z.2 v).length < (finiteWordMap z.2 u).length

/-- A genuine tree map passes every finite test. -/
theorem treeMapFiniteTest_of_witness {ε : ℕ → ℕ}
    (T S : PairTree ε) (rootTest : finseq ℕ → Prop) (x q : ℕ → ℕ)
    (hroot : rootTest (codedWordMap q []))
    (hmap : IsTreeMapWitness (rootedSection T x) (rootedSection S x) (codedWordMap q)) :
    ∀ n, treeMapFiniteTest T.tree S.tree rootTest (seqPrefix x n, seqPrefix q n) := by
  intro n
  constructor
  · intro hn
    rw [finiteWordMap_prefix q [] n (by simpa [seqPrefix_length] using hn)]
    exact hroot
  · intro i hi u hu hui hul huT
    simp only [seqPrefix_length] at hi hui hul
    have hTu := (finiteSectionNode_prefix T x u n hul).mp huT
    rw [finiteWordMap_prefix q u n hui]
    constructor
    · intro hlen
      exact (finiteSectionNode_prefix S x _ n (by simpa [seqPrefix_length] using hlen)).mpr
        (hmap.1 u hTu)
    · intro j hj v hv hvj hvu hlen
      rw [finiteWordMap_prefix q v n (by simpa [seqPrefix_length] using hvj)]
      exact hmap.2 u hTu v hvu hlen

/-- Every individual map obligation is checked once enough coordinates of
both the point and the map are present. -/
theorem witness_of_treeMapFiniteTest {ε : ℕ → ℕ}
    (T S : PairTree ε) (rootTest : finseq ℕ → Prop) (x q : ℕ → ℕ)
    (h : ∀ n, treeMapFiniteTest T.tree S.tree rootTest (seqPrefix x n, seqPrefix q n)) :
    rootTest (codedWordMap q []) ∧
      IsTreeMapWitness (rootedSection T x) (rootedSection S x) (codedWordMap q) := by
  refine ⟨?_, ?_, ?_⟩
  · have hr := (h (NatListCode.encode ([] : finseq ℕ) + 1)).1 (by simp [seqPrefix_length])
    simpa only [finiteWordMap_prefix q [] _ (Nat.lt_succ_self _)] using hr
  · intro u hu
    let n := max (NatListCode.encode u + 1) (max u.length (codedWordMap q u).length)
    have hcode : NatListCode.encode u < n := by dsimp [n]; omega
    have hlen : u.length ≤ n := by dsimp [n]; omega
    have hout : (codedWordMap q u).length ≤ n := by dsimp [n]; omega
    have huT := (finiteSectionNode_prefix T x u n hlen).mpr hu
    have hc := (h n).2 (NatListCode.encode u) (by simpa [seqPrefix_length] using hcode)
      u (wordOfCode_encode u).symm (by simpa [seqPrefix_length] using hcode)
      (by simpa [seqPrefix_length] using hlen) huT
    rw [finiteWordMap_prefix q u n hcode] at hc
    exact (finiteSectionNode_prefix S x _ n hout).mp
      (hc.1 (by simpa [seqPrefix_length] using hout))
  · intro u hu v hv hlen
    let n := max (NatListCode.encode u + 1) (max (NatListCode.encode v + 1) u.length)
    have hcode : NatListCode.encode u < n := by dsimp [n]; omega
    have hvcode : NatListCode.encode v < n := by dsimp [n]; omega
    have hulen : u.length ≤ n := by dsimp [n]; omega
    have huT := (finiteSectionNode_prefix T x u n hulen).mpr hu
    have hc := (h n).2 (NatListCode.encode u) (by simpa [seqPrefix_length] using hcode)
      u (wordOfCode_encode u).symm (by simpa [seqPrefix_length] using hcode)
      (by simpa [seqPrefix_length] using hulen) huT
    have hp := hc.2 (NatListCode.encode v) (by simpa [seqPrefix_length] using hvcode)
      v (wordOfCode_encode v).symm (by simpa [seqPrefix_length] using hvcode) hv hlen
    simpa only [finiteWordMap_prefix q u n hcode, finiteWordMap_prefix q v n hvcode] using hp

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Finite comparison-map tests
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    A genuine map passes every test: if $c(u)<n$, then $f_{\restrict{q}{n}}(u)=f_q(u)$, and if $|u|\le n$,
    the finite section test at $\restrict{x}{n}$ agrees with membership in $T_x$.
    Conversely, suppose every prefix test passes. The root is checked at length one. For any $u\in T_x$,
    choose $n\ge\max\{c(u)+1,|u|,|f_q(u)|\}$. The image-membership test then proves $f_q(u)\in S_x$.
    For a strict prefix $v$ of $u$, choose $n\ge\max\{c(u)+1,c(v)+1,|u|\}$; the edge test proves strict
    extension preservation. These bounds are used to verify the construction, not to compute the infinite map.
    The finite tests use only list access, lengths, prefixes, the two tree deciders, and two bounded loops.
    Their explicit lambda programs in §{sec:lambda-comparison-programs} use the original parameter throughout.
    \end{proof}
-/
theorem all_treeMapFiniteTest_iff {ε : ℕ → ℕ}
    (T S : PairTree ε) (rootTest : finseq ℕ → Prop) (x q : ℕ → ℕ) :
    (∀ n, treeMapFiniteTest T.tree S.tree rootTest (seqPrefix x n, seqPrefix q n)) ↔
      rootTest (codedWordMap q []) ∧
      IsTreeMapWitness (rootedSection T x) (rootedSection S x) (codedWordMap q) :=
  ⟨witness_of_treeMapFiniteTest T S rootTest x q,
    fun h => treeMapFiniteTest_of_witness T S rootTest x q h.1 h.2⟩

end LambdaTree
end PolishSpaceBook
