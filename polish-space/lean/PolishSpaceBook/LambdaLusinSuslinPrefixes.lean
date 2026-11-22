module

public import PolishSpaceBook.LambdaEffectiveSeparation

@[expose] public section

/-! # Uniform separated prefix tests for a closed graph with unique sections

The first coordinate is the output and the second is its possible preimage.
All syntax transformations are total; uniqueness is used only to justify the
separation and the recovered prefix tests on the projection.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance lusinPrefixListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance lusinPrefixPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $p,K,O,Z, \ell$ from §{sec:lambda-comparison-programs}. Keep the output-first, input-second tree order. For
    a prefix code $j$ and an input-word code $v$, put
    $$\begin{aligned}
    \LambdaTermName{prefixGate}_+(j,v)&:=O\bigl(p(j,v),p(v,j)\bigr),\\
    \LambdaTermName{prefixGate}_-(j,v)&:=O\bigl(K(\ell(v),\ell(j)),Zp(j,v)\bigr).
    \end{aligned}$$
    The first tests prefix compatibility. The second accepts a word shorter than the supplied prefix,
    or a word that does not extend it. Let $P$ be the fixed joint decider for the indexed pair trees.
    From $z=\NatPair{\NatPair{e}{j}}{\NatPair{u}{v}}$ extract its four numerical fields by projections and set
    $$\LambdaTermName{slice}_\pm:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
     \bigl(Po(\LambdaNumericPair\,e\,(\LambdaNumericPair\,u\,v))\bigr)\,\LambdaTermName{prefixGate}_\pm(j,v)}}.$$
    Expand the abbreviations with fresh binders. Check equal lengths and apply the finite-check-tree
    construction to this test: it checks every simultaneous prefix, including the empty pair.
    This gives two jointly decidable tree families. Specializing their fixed joint deciders produces
    total index maps $\alpha_+(e,j),\alpha_-(e,j)$. If $\operatorname{sep},\operatorname{co}$ are the two separation
    index maps, use
    $$\begin{aligned}
    c(e,j)&:=\operatorname{sep}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr),\\
    d(e,j)&:=\operatorname{co}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr).
    \end{aligned}$$
-/
def witnessPrefixGate (positive : Bool) (s v : List ℕ) : Prop :=
  if positive then prefixCompatible s v else v.length < s.length ∨ ¬ prefixOf s v

theorem all_witnessPrefixGate_iff (positive : Bool) (s : List ℕ) (x : ℕ → ℕ) :
    (∀ n, witnessPrefixGate positive s (seqPrefix x n)) ↔
      if positive then x ∈ cyl s else x ∉ cyl s := by
  cases positive with
  | true => simpa only [witnessPrefixGate,ite_true] using all_prefixCompatible_iff s x
  | false =>
    simp only [witnessPrefixGate,Bool.false_eq_true,ite_false]
    constructor
    · intro h hx
      have hn := h s.length
      rw [seqPrefix_length] at hn
      rcases hn with hn | hn
      · exact (lt_irrefl _ hn).elim
      · exact hn (by rw [seqPrefix_eq_of_mem_cyl hx])
    · intro hx n
      right
      intro hs
      exact hx (prefixOfSeq_of_prefix hs (prefixOfSeq_seqPrefix x n))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $p,K,O,Z, \ell$ from §{sec:lambda-comparison-programs}. Keep the output-first, input-second tree order. For
    a prefix code $j$ and an input-word code $v$, put
    $$\begin{aligned}
    \LambdaTermName{prefixGate}_+(j,v)&:=O\bigl(p(j,v),p(v,j)\bigr),\\
    \LambdaTermName{prefixGate}_-(j,v)&:=O\bigl(K(\ell(v),\ell(j)),Zp(j,v)\bigr).
    \end{aligned}$$
    The first tests prefix compatibility. The second accepts a word shorter than the supplied prefix,
    or a word that does not extend it. Let $P$ be the fixed joint decider for the indexed pair trees.
    From $z=\NatPair{\NatPair{e}{j}}{\NatPair{u}{v}}$ extract its four numerical fields by projections and set
    $$\LambdaTermName{slice}_\pm:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
     \bigl(Po(\LambdaNumericPair\,e\,(\LambdaNumericPair\,u\,v))\bigr)\,\LambdaTermName{prefixGate}_\pm(j,v)}}.$$
    Expand the abbreviations with fresh binders. Check equal lengths and apply the finite-check-tree
    construction to this test: it checks every simultaneous prefix, including the empty pair.
    This gives two jointly decidable tree families. Specializing their fixed joint deciders produces
    total index maps $\alpha_+(e,j),\alpha_-(e,j)$. If $\operatorname{sep},\operatorname{co}$ are the two separation
    index maps, use
    $$\begin{aligned}
    c(e,j)&:=\operatorname{sep}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr),\\
    d(e,j)&:=\operatorname{co}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr).
    \end{aligned}$$
-/
theorem witnessPrefixGate_decidable (ε : ℕ → ℕ) (positive : Bool) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      witnessPrefixGate positive (NatListCode.decode z.unpair.1) (NatListCode.decode z.unpair.2)) := by
  cases positive with
  | true =>
    exact (word_prefix_decidable (projection_computes true) (projection_computes false) ε).or
      (word_prefix_decidable (projection_computes false) (projection_computes true) ε)
  | false =>
    exact (numerical_lt_decidable (listLength_computes.comp (projection_computes false))
      (listLength_computes.comp (projection_computes true)) ε).or
      (word_prefix_decidable (projection_computes true) (projection_computes false) ε).not

def witnessSliceTest (ε : ℕ → ℕ) (positive : Bool) (i : ℕ) (z : List ℕ × List ℕ) : Prop :=
  z ∈ (indexedTree ε i.unpair.1).tree ∧ witnessPrefixGate positive (NatListCode.decode i.unpair.2) z.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $p,K,O,Z, \ell$ from §{sec:lambda-comparison-programs}. Keep the output-first, input-second tree order. For
    a prefix code $j$ and an input-word code $v$, put
    $$\begin{aligned}
    \LambdaTermName{prefixGate}_+(j,v)&:=O\bigl(p(j,v),p(v,j)\bigr),\\
    \LambdaTermName{prefixGate}_-(j,v)&:=O\bigl(K(\ell(v),\ell(j)),Zp(j,v)\bigr).
    \end{aligned}$$
    The first tests prefix compatibility. The second accepts a word shorter than the supplied prefix,
    or a word that does not extend it. Let $P$ be the fixed joint decider for the indexed pair trees.
    From $z=\NatPair{\NatPair{e}{j}}{\NatPair{u}{v}}$ extract its four numerical fields by projections and set
    $$\LambdaTermName{slice}_\pm:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
     \bigl(Po(\LambdaNumericPair\,e\,(\LambdaNumericPair\,u\,v))\bigr)\,\LambdaTermName{prefixGate}_\pm(j,v)}}.$$
    Expand the abbreviations with fresh binders. Check equal lengths and apply the finite-check-tree
    construction to this test: it checks every simultaneous prefix, including the empty pair.
    This gives two jointly decidable tree families. Specializing their fixed joint deciders produces
    total index maps $\alpha_+(e,j),\alpha_-(e,j)$. If $\operatorname{sep},\operatorname{co}$ are the two separation
    index maps, use
    $$\begin{aligned}
    c(e,j)&:=\operatorname{sep}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr),\\
    d(e,j)&:=\operatorname{co}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr).
    \end{aligned}$$
-/
theorem witnessSliceTest_family_decidable (ε : ℕ → ℕ) (positive : Bool) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      witnessSliceTest ε positive z.1 z.2) := by
  have ht := indexedTree_reindex_decidable ε (projection_computes true)
  have hg := (witnessPrefixGate_decidable ε positive).precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => Nat.pair z.1.unpair.2 (NatListCode.encode z.2.2))
    (((projection_computes false).comp (projection_computes true)).pair
      ((projection_computes false).comp (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  simpa only [Nat.unpair_pair,NatListCode.decode_encode,witnessSliceTest,ite_true] using ht.and hg

def witnessSliceTree (ε : ℕ → ℕ) (positive : Bool) (i : ℕ) : PairTree ε :=
  finiteCheckTree (witnessSliceTest ε positive i)
    ((witnessSliceTest_family_decidable ε positive).precompNumerical
      (g := fun z : List ℕ × List ℕ => (i,z))
      ((numericalConstant_computes i).pair numericalIdentity_computes)
      (fun z => by simp [Encodable.encode,Encodable.encodeSigma]))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The indexed family decider, list lengths, prefix comparisons, and bit operations are total.
    The finite-check construction therefore terminates and enforces all tests along a branch.
    Compatibility with every finite prefix of a sequence is equivalent to membership in the cylinder.
    For the negative test, a sequence outside the cylinder never extends its defining word, so every
    test accepts. A sequence in the cylinder fails the test as soon as the defining length is reached.
    Thus the two branch conditions are precisely the asserted restrictions. No uniqueness or
    nonemptiness test occurs in either decider or in the numerical specialization maps.
-/
theorem witnessSliceTree_family_decidable (ε : ℕ → ℕ) (positive : Bool) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (witnessSliceTree ε positive z.1).tree) :=
  finiteCheck_family_decidable (witnessSliceTest_family_decidable ε positive)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Preimage prefix slice programs
-/
theorem pairTreeBody_witnessSliceTree (ε : ℕ → ℕ) (positive : Bool) (e s : ℕ)
    (y x : ℕ → ℕ) :
    (y,x) ∈ pairTreeBody (witnessSliceTree ε positive (Nat.pair e s)).tree ↔
      (y,x) ∈ pairTreeBody (indexedTree ε e).tree ∧
        if positive then x ∈ cyl (NatListCode.decode s) else x ∉ cyl (NatListCode.decode s) := by
  change (y,x) ∈ pairTreeBody (finiteCheckNodes _) ↔ _
  rw [pairTreeBody_finiteCheckNodes]
  simp only [witnessSliceTest,Nat.unpair_pair,forall_and,all_witnessPrefixGate_iff,pairTreeBody,
    mem_ofPred_eq]

/-- A closed relation whose output determines at most one input. -/
def UniqueSections (T : Set (List ℕ × List ℕ)) : Prop :=
  ∀ y x x', (y,x) ∈ pairTreeBody T → (y,x') ∈ pairTreeBody T → x = x'

theorem witnessSliceTree_disjoint (ε : ℕ → ℕ) (e s : ℕ)
    (hu : UniqueSections (indexedTree ε e).tree) :
    Disjoint (pairTreeProjection (witnessSliceTree ε true (Nat.pair e s)).tree)
      (pairTreeProjection (witnessSliceTree ε false (Nat.pair e s)).tree) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x,hx⟩ ⟨x',hx'⟩
  have hp := (pairTreeBody_witnessSliceTree ε true e s y x).mp hx
  have hn := (pairTreeBody_witnessSliceTree ε false e s y x').mp hx'
  simp only [ite_true,Bool.false_eq_true,ite_false] at hp hn
  exact hn.2 ((hu y x x' hp.1 hn.1) ▸ hp.2)

/-- The same numerical transformations work for every graph index and prefix. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Uniform separated preimage prefix tests
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Let $A_s^+$ and $A_s^-$ be the projections obtained by requiring the second coordinate to belong
    to $\cyl{s}$ and its complement, respectively. The finite tests of
    §{sec:lambda-closed-graph-indices} give both presentations jointly in the tree index and word code.
    Uniqueness makes these projections disjoint: two preimages of the same output must coincide and
    cannot satisfy opposite prefix tests. Apply uniform separation to obtain
    $$A_s^+\IncludedIn C_s\IncludedIn(A_s^-)^{\complement},\qquad C_s=(C'_s)^{\complement}.$$
    On a graph pair the second coordinate either belongs to the cylinder, placing the output in the
    first projection, or fails to belong, placing it in the second. This proves the displayed equivalence.
    The two numerical index maps are compositions of the slice generators and the separation generators.
    All these generators are total before the uniqueness assumption is imposed.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $p,K,O,Z, \ell$ from §{sec:lambda-comparison-programs}. Keep the output-first, input-second tree order. For
    a prefix code $j$ and an input-word code $v$, put
    $$\begin{aligned}
    \LambdaTermName{prefixGate}_+(j,v)&:=O\bigl(p(j,v),p(v,j)\bigr),\\
    \LambdaTermName{prefixGate}_-(j,v)&:=O\bigl(K(\ell(v),\ell(j)),Zp(j,v)\bigr).
    \end{aligned}$$
    The first tests prefix compatibility. The second accepts a word shorter than the supplied prefix,
    or a word that does not extend it. Let $P$ be the fixed joint decider for the indexed pair trees.
    From $z=\NatPair{\NatPair{e}{j}}{\NatPair{u}{v}}$ extract its four numerical fields by projections and set
    $$\LambdaTermName{slice}_\pm:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
     \bigl(Po(\LambdaNumericPair\,e\,(\LambdaNumericPair\,u\,v))\bigr)\,\LambdaTermName{prefixGate}_\pm(j,v)}}.$$
    Expand the abbreviations with fresh binders. Check equal lengths and apply the finite-check-tree
    construction to this test: it checks every simultaneous prefix, including the empty pair.
    This gives two jointly decidable tree families. Specializing their fixed joint deciders produces
    total index maps $\alpha_+(e,j),\alpha_-(e,j)$. If $\operatorname{sep},\operatorname{co}$ are the two separation
    index maps, use
    $$\begin{aligned}
    c(e,j)&:=\operatorname{sep}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr),\\
    d(e,j)&:=\operatorname{co}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr).
    \end{aligned}$$
-/
theorem uniform_separated_prefix_indices (ε : ℕ → ℕ) :
    ∃ (C D : AlphaTerm) (c d : ℕ → ℕ), NumericalComputes C c ∧ NumericalComputes D d ∧
      ∀ e, UniqueSections (indexedTree ε e).tree → ∀ s,
        indexedProjection ε (c (Nat.pair e s)) = (indexedProjection ε (d (Nat.pair e s)))ᶜ ∧
        ∀ y x, (y,x) ∈ pairTreeBody (indexedTree ε e).tree →
          (y ∈ indexedProjection ε (c (Nat.pair e s)) ↔ x ∈ cyl (NatListCode.decode s)) := by
  obtain ⟨p,⟨P,hP⟩,hp⟩ := treeFamily_indices ε (witnessSliceTree ε true)
    (witnessSliceTree_family_decidable ε true)
  obtain ⟨q,⟨Q,hQ⟩,hq⟩ := treeFamily_indices ε (witnessSliceTree ε false)
    (witnessSliceTree_family_decidable ε false)
  obtain ⟨sep,co,⟨S,hS⟩,⟨R,hR⟩,hsep⟩ := exists_separationIndices ε
  refine ⟨_,_,_,_,hS.comp (hP.pair hQ),hR.comp (hP.pair hQ),fun e hu s => ?_⟩
  have hep : indexedProjection ε (p (Nat.pair e s)) =
      pairTreeProjection (witnessSliceTree ε true (Nat.pair e s)).tree :=
    pairTreeProjection_indexedTree ε _ _ (hp _)
  have heq : indexedProjection ε (q (Nat.pair e s)) =
      pairTreeProjection (witnessSliceTree ε false (Nat.pair e s)).tree :=
    pairTreeProjection_indexedTree ε _ _ (hq _)
  have hdis : Disjoint (indexedProjection ε (p (Nat.pair e s)))
      (indexedProjection ε (q (Nat.pair e s))) := by
    rw [hep,heq]
    exact witnessSliceTree_disjoint ε e s hu
  obtain ⟨hl,hr,hc⟩ := hsep (p (Nat.pair e s)) (q (Nat.pair e s)) hdis
  refine ⟨hc,fun y x hx => ⟨?_,?_⟩⟩
  · intro hy
    by_contra hn
    apply hr hy
    rw [heq]
    refine ⟨x,(pairTreeBody_witnessSliceTree ε false e s y x).mpr ?_⟩
    exact ⟨hx,hn⟩
  · intro hs
    apply hl
    rw [hep]
    refine ⟨x,(pairTreeBody_witnessSliceTree ε true e s y x).mpr ?_⟩
    exact ⟨hx,hs⟩

/-- The first accepted word of a specified length, ordered by numerical word code. -/
def firstAcceptedPrefix (C : List ℕ → Set (ℕ → ℕ)) (s : List ℕ) (y : ℕ → ℕ) : Prop :=
  y ∈ C s ∧ ∀ j < NatListCode.encode s,
    (NatListCode.decode j).length = s.length → y ∉ C (NatListCode.decode j)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The sets $C_s$ may overlap away from the image. Make their tests disjoint at each length and
    compatible under restriction. Write $w_j$ for the unique word with $\LambdaListCode{w_j}=j$. Define
    $$\begin{aligned}
    B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\\Length{w_j}=\Length{s}}}C_{w_j}},\\
    H_s&:=\bigcap_{0\le n\le\Length{s}}B_{\restrict{s}{n}}.
    \end{aligned}$$
    Only finitely many tests occur in each expression. At a fixed length the sets $B_s$ are disjoint,
    and $t\extendsPrefix s$ implies $H_t\IncludedIn H_s$. On the graph, an output belongs to $H_s$
    exactly when its preimage belongs to $\cyl{s}$.
-/
def coherentPrefix (C : List ℕ → Set (ℕ → ℕ)) (s : List ℕ) (y : ℕ → ℕ) : Prop :=
  ∀ n ≤ s.length, firstAcceptedPrefix C (s.take n) y

theorem firstAcceptedPrefix_unique {C : List ℕ → Set (ℕ → ℕ)} {s t : List ℕ} {y : ℕ → ℕ}
    (hs : firstAcceptedPrefix C s y) (ht : firstAcceptedPrefix C t y) (hl : s.length = t.length) : s = t := by
  rcases lt_trichotomy (NatListCode.encode s) (NatListCode.encode t) with h | h | h
  · exact False.elim (ht.2 _ h (by simpa only [NatListCode.decode_encode] using hl)
      (by simpa only [NatListCode.decode_encode] using hs.1))
  · simpa only [NatListCode.decode_encode] using congrArg NatListCode.decode h
  · exact False.elim (hs.2 _ h (by simpa only [NatListCode.decode_encode] using hl.symm)
      (by simpa only [NatListCode.decode_encode] using ht.1))

theorem coherentPrefix_take {C : List ℕ → Set (ℕ → ℕ)} {s : List ℕ} {y : ℕ → ℕ}
    (hs : coherentPrefix C s y) (n : ℕ) : coherentPrefix C (s.take n) y := by
  intro k hk
  have hkn : k ≤ n := (by simpa only [List.length_take] using hk : k ≤ min n s.length).trans (min_le_left _ _)
  have hks : k ≤ s.length := (by simpa only [List.length_take] using hk : k ≤ min n s.length).trans (min_le_right _ _)
  simpa only [List.take_take,min_eq_left hkn] using hs k hks

theorem coherentPrefix_unique {C : List ℕ → Set (ℕ → ℕ)} {s t : List ℕ} {y : ℕ → ℕ}
    (hs : coherentPrefix C s y) (ht : coherentPrefix C t y) (hl : s.length = t.length) : s = t := by
  apply firstAcceptedPrefix_unique (y := y) (C := C) _ _ hl
  · simpa only [List.take_length] using hs s.length le_rfl
  · simpa only [List.take_length] using ht t.length le_rfl

theorem firstAcceptedPrefix_of_exact_tests {C : List ℕ → Set (ℕ → ℕ)} {y x : ℕ → ℕ}
    (hc : ∀ s, y ∈ C s ↔ x ∈ cyl s) {s : List ℕ} (hx : x ∈ cyl s) :
    firstAcceptedPrefix C s y := by
  refine ⟨(hc s).mpr hx,fun j hj hl hy => ?_⟩
  have hxj := (hc _).mp hy
  have he : NatListCode.decode j = s := by
    rw [← seqPrefix_eq_of_mem_cyl hxj,hl,seqPrefix_eq_of_mem_cyl hx]
  have he' := congrArg NatListCode.encode he
  rw [NatListCode.encode_decode] at he'
  omega

theorem coherentPrefix_of_exact_tests {C : List ℕ → Set (ℕ → ℕ)} {y x : ℕ → ℕ}
    (hc : ∀ s, y ∈ C s ↔ x ∈ cyl s) {s : List ℕ} (hx : x ∈ cyl s) :
    coherentPrefix C s y := by
  intro n hn
  exact firstAcceptedPrefix_of_exact_tests hc (prefixOfSeq_of_prefix (List.take_prefix n s) hx)

/-- Compatible words of every prescribed length determine an infinite sequence. -/
theorem sequence_of_prefix_family (s : ℕ → List ℕ) (hl : ∀ n, (s n).length = n)
    (hp : ∀ n m, n ≤ m → prefixOf (s n) (s m)) :
    ∃ x : ℕ → ℕ, ∀ n, seqPrefix x n = s n := by
  let x := fun i => (s (i+1)).get ⟨i,by rw [hl]; omega⟩
  refine ⟨x,fun n => ?_⟩
  have hx : x ∈ cyl (s n) := by
    intro i hi
    have hin : i < n := by simpa only [hl] using hi
    exact (hp (i+1) n (by omega)).getElem (by rw [hl]; omega)
  simpa only [hl] using seqPrefix_eq_of_mem_cyl hx

/-- Only finite tree membership and the coherent prefix tests enter the image formula. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Closed graph image by coherent prefix tests
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    If $\Pair{y}{x}\in[T_e]$, choose $s=\restrict{x}{n}$ at every length. The graph-prefix equivalence gives
    $y\in H_s$, and the branch condition gives membership of the finite pair.
    Conversely, choose a word $s_n$ at every length on the right-hand side. For $n\le m$, the word
    $\restrict{s_m}{n}$ has length $n$, and the output belongs to its coherent test. Disjointness at that
    length forces $s_n=\restrict{s_m}{n}$. These compatible words define a sequence $x$ with
    $\restrict{x}{n}=s_n$ for all $n$. Every finite pair belongs to the tree, so $\Pair{y}{x}\in[T_e]$.
    The argument includes the empty-graph case: satisfying the right-hand side would produce a branch.
-/
theorem projection_iff_coherent_prefix_tests (T : Set (List ℕ × List ℕ))
    (C : List ℕ → Set (ℕ → ℕ))
    (hc : ∀ y x, (y,x) ∈ pairTreeBody T → ∀ s, y ∈ C s ↔ x ∈ cyl s) (y : ℕ → ℕ) :
    y ∈ pairTreeProjection T ↔
      ∀ n, ∃ s : List ℕ, s.length = n ∧ coherentPrefix C s y ∧ (seqPrefix y n,s) ∈ T := by
  constructor
  · rintro ⟨x,hx⟩ n
    exact ⟨seqPrefix x n,seqPrefix_length x n,
      coherentPrefix_of_exact_tests (hc y x hx) (mem_cyl_seqPrefix x n),hx n⟩
  · intro hy
    choose s hl hs ht using hy
    have hp (n m : ℕ) (hnm : n ≤ m) : prefixOf (s n) (s m) := by
      have he : s n = (s m).take n := coherentPrefix_unique (hs n)
        (coherentPrefix_take (hs m) n) (by simp only [hl,List.length_take,min_eq_left hnm])
      rw [he]
      exact List.take_prefix n (s m)
    obtain ⟨x,hx⟩ := sequence_of_prefix_family s hl hp
    exact ⟨x,fun n => by simpa only [hx n] using ht n⟩

/-- Restricting the unique preimage to a cylinder becomes a prefix test on the image. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The inverse prefix sets satisfy the exact identity
    $$\{y:\exists x\ (\Pair{y}{x}\in[T_e]\land x\in\cyl{s})\}
       =\pi_0([T_e])\cap C_s.$$
    For a graph of an injection, the left-hand side is the inverse image of the domain cylinder under
    the inverse map. The separated test supplies its restriction to the image; the image formula
    supplies the additional condition that the output actually has a preimage.
-/
theorem witness_prefix_projection_eq (T : Set (List ℕ × List ℕ))
    (C : List ℕ → Set (ℕ → ℕ))
    (hc : ∀ y x, (y,x) ∈ pairTreeBody T → ∀ s, y ∈ C s ↔ x ∈ cyl s) (s : List ℕ) :
    {y | ∃ x, (y,x) ∈ pairTreeBody T ∧ x ∈ cyl s} = pairTreeProjection T ∩ C s := by
  ext y
  constructor
  · rintro ⟨x,hx,hs⟩
    exact ⟨⟨x,hx⟩,(hc y x hx s).mpr hs⟩
  · rintro ⟨⟨x,hx⟩,hy⟩
    exact ⟨x,hx,(hc y x hx s).mp hy⟩

end LambdaTree
end PolishSpaceBook
