module

public import PolishSpaceBook.JointTreeRankBound
public import PolishSpaceBook.BorelExpressionBoolean
public import PolishSpaceBook.BorelExpressionNatCertificates

@[expose] public section

/-! # Explicit open codes for edges of a section tree

Every edge is tested from one finite prefix of the point. Enumerating all
prefixes of the required length gives a countable union of cylinders, with
empty expressions at rejected indices. This choice is decidable from the
original pair-tree membership test.
-/
namespace PolishSpaceBook
open Set NamedLambda BorelExpression
namespace LambdaTree

def sectionEdgeGuard {ε : ℕ → ℕ} (S : PairTree ε) (b a k : ℕ) : Prop :=
  prefixOf (NatListCode.decode a) (NatListCode.decode b) ∧
    (NatListCode.decode a).length < (NatListCode.decode b).length ∧
    (NatListCode.decode k).length = (NatListCode.decode b).length ∧
    (NatListCode.decode k,NatListCode.decode b) ∈ S.tree

noncomputable def sectionEdgeCode {ε : ℕ → ℕ} (S : PairTree ε) (b a : ℕ) : Code := by
  classical
  exact Code.iUnion (fun k => if sectionEdgeGuard S b a k then Code.leaf k else Code.empty)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The edge relation has a uniform open code. Write
    $$H(b,a,k)\quad\Longleftrightarrow\quad
    u_a\prefixOf u_b,\quad \Length{u_a}<\Length{u_b},\quad \Length{u_k}=\Length{u_b},\quad\Pair{u_k}{u_b}\in S.$$
    Then
    $$\begin{aligned}
    f_{b,a,k}&:=\begin{cases}\BorelLeafCode{k}&H(b,a,k),\\
                             \BorelEmptyCode&\neg H(b,a,k),\end{cases}\\
    e_{b,a}&:=\BorelUnionCode{\Sequence{f_{b,a,k}}{k\in\omega}},\\
    \BorelValue{e_{b,a}}&=\{x:E_x(b,a)\}.
    \end{aligned}$$
    Indeed, a cylinder selected by $H$ makes $u_b$ a node of $S_x$, and its prefix $u_a$ is then a node
    as well. Conversely, an edge supplies the selected cylinder with word $\restrict{x}{\Length{u_b}}$.
    The union and leaf label programs, together with the decision of $H$, compute $e_{b,a}(v)$ jointly in
    $b,a,\LambdaListCode{v}$.
    The explicit closed terms for this and the relation $R$ appear in §{sec:lambda-recursive-borel-separation}.
-/
theorem mem_sectionEdgeCode {ε : ℕ → ℕ} (S : PairTree ε) (b a : ℕ) (x : ℕ → ℕ) :
    x ∈ (sectionEdgeCode S b a).value cylinderBasis ↔
      (rootedSection S x).codedExtension b a := by
  classical
  have h0 : cylinderBasis 0 = univ := by simp [cylinderBasis,NatListCode.decode]
  have he : x ∈ (sectionEdgeCode S b a).value cylinderBasis ↔
      ∃ k, sectionEdgeGuard S b a k ∧ x ∈ cyl (NatListCode.decode k) := by
    simp only [sectionEdgeCode,Code.value_iUnion,mem_iUnion]
    apply exists_congr
    intro k
    by_cases h : sectionEdgeGuard S b a k <;>
      simp [h,Code.value_leaf,Code.value_empty cylinderBasis h0,cylinderBasis]
  rw [he]
  constructor
  · rintro ⟨k,⟨hp,hl,hlen,hm⟩,hx⟩
    have hs : seqPrefix x (NatListCode.decode b).length = NatListCode.decode k := by
      rw [← hlen]
      exact seqPrefix_eq_of_mem_cyl hx
    have hb : NatListCode.decode b ∈ (rootedSection S x).tree :=
      Or.inr (by simpa only [hs] using hm)
    exact ⟨hb,(rootedSection S x).downward hb hp,hp,hl⟩
  · intro h
    have hb : (seqPrefix x (NatListCode.decode b).length,NatListCode.decode b) ∈ S.tree := by
      rcases h.1 with he | hm
      · have hl := h.2.2.2
        simp only [he,List.length_nil] at hl
        omega
      · exact hm
    refine ⟨NatListCode.encode (seqPrefix x (NatListCode.decode b).length),?_,?_⟩
    · simpa only [sectionEdgeGuard,NatListCode.decode_encode,seqPrefix_length] using
        (show prefixOf (NatListCode.decode a) (NatListCode.decode b) ∧
          (NatListCode.decode a).length < (NatListCode.decode b).length ∧
          (NatListCode.decode b).length = (NatListCode.decode b).length ∧
          (seqPrefix x (NatListCode.decode b).length,NatListCode.decode b) ∈ S.tree from
          ⟨h.2.2.1,h.2.2.2,rfl,hb⟩)
    · simpa only [NatListCode.decode_encode] using mem_cyl_seqPrefix x (NatListCode.decode b).length

end LambdaTree
end PolishSpaceBook
