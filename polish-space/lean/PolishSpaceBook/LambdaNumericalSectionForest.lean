module

public import PolishSpaceBook.LambdaJointRankBound
public import PolishSpaceBook.LambdaListTabulation

@[expose] public section

/-! # One recursive forest for all numerical sections of a pair tree

The first component selects the constant sequence n,n,...; the second is a
word code. Edges never change the first component. All membership and edge
tests are concrete numerical lambda computations at the original parameter.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative
namespace LambdaTree
local instance numericalSectionsPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Input (n,k) produces the code of k copies of n. -/
def constantPrefixProgram := listTabulateTerm (numericalProjectionTerm true)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let $S$ be a pair tree whose membership is decided by $P$ at parameter $\varepsilon$. Write
    $x_n(k)=n$ and $S_n:=\{t:t=[]\lor(\restrict{x_n}{|t|},t)\in S\}$. Put
    $p_i:=\LambdaNumericProjection{i}$ for $i=1,2$ and define
    $$\begin{aligned}
     Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
     O(d,e)&:=Z(\LambdaMul\,(Zd)\,(Ze)),\\
     C&:=\LambdaListTabulate{p_1},\\
     F(z)&:=\LambdaNumericPair\,
      \bigl(C(\LambdaNumericPair\,(p_1z)\,(\LambdaListLength\,(p_2z)))\bigr)\,(p_2z),\\
     M&:=\lambdaab{o}{\lambdaab{z}{O(Z(p_2z),Po(F(z)))}}.
    \end{aligned}$$
    Expand the abbreviation $F$ and the Boolean body before abstraction. On input $\NatPair{n}{k}$, the term
    $C$ computes the code of the length-$k$ constant word with value $n$.
-/
theorem constantPrefix_computes : NumericalComputes constantPrefixProgram
    (fun z => NatListCode.encode (seqPrefix (fun _ => z.unpair.1) z.unpair.2)) := by
  have h := listTabulate_computes (projection_computes true)
  refine ⟨h.1,fun z => ?_⟩
  have he : (List.range z.unpair.2).map (fun k => (Nat.unpair (Nat.pair z.unpair.1 k)).1) =
      seqPrefix (fun _ => z.unpair.1) z.unpair.2 := by
    apply List.ext_getElem <;> simp [seqPrefix]
  simpa only [constantPrefixProgram,ite_true,he] using h.2 z

theorem numericalSection_decidable {ε : ℕ → ℕ} (S : PairTree ε) :
    DecidablePredicate ε (fun z : ℕ =>
      NatListCode.decode z.unpair.2 ∈ (rootedSection S (fun _ => z.unpair.1)).tree) := by
  have hp := constantPrefix_computes.comp
    ((projection_computes true).pair (listLength_computes.comp (projection_computes false)))
  have ht := S.decidable.precompNumerical (hp.pair (projection_computes false))
    (g := fun z : ℕ => (seqPrefix (fun _ => z.unpair.1) (NatListCode.decode z.unpair.2).length,
      NatListCode.decode z.unpair.2)) (fun z => by simp [Encodable.encode])
  simpa only [rootedSection,mem_ofPred_eq,decode_eq_nil_iff,Bool.false_eq_true,ite_false] using
    (numerical_zero_decidable (projection_computes false) ε).or ht

/-- Each component is a coded strict-extension relation. -/
def sectionForest {ε : ℕ → ℕ} (S : PairTree ε) (b a : ℕ) : Prop :=
  b.unpair.1 = a.unpair.1 ∧
    (rootedSection S (fun _ => a.unpair.1)).codedExtension b.unpair.2 a.unpair.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Recursive numerical section forests
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Finite tabulation of the first projection appends the unchanged first input at each step, proving the
    assertion about $C$. The list code is zero exactly for the empty word. Thus $M$ accepts that word.
    The term $F$ supplies exactly the paired codes required by the decider for $S$. This proves the
    membership assertion, including the case where the original pair tree has no root.

    For the edge test, decode $z=\NatPair{u}{v}$ and put
    $$L(d,e):=\LambdaLeCase{d}{e}{\ChurchNumeral{1}}{\ChurchNumeral{0}}.$$
    Use the following product of bits, with each product implemented by $\LambdaMul$:
    $$\begin{aligned}
     D(o,z):={}&L(p_1u,p_1v)\,L(p_1v,p_1u)\\
     &\cdot M o(\LambdaNumericPair\,(p_1v)\,(p_2u))\cdot M o v\\
     &\cdot\LambdaListPrefix(\LambdaNumericPair\,(p_2v)\,(p_2u))\\
     &\cdot L(\LambdaSucc(\LambdaListLength\,(p_2v)),\LambdaListLength\,(p_2u)).
    \end{aligned}$$
    Substitute $u=p_1z$, $v=p_2z$ and expand all abbreviations before forming
    $\lambdaab{o}{\lambdaab{z}{D(o,z)}}$. The two comparisons test equality of the component indices.
    The other factors test the two memberships, the prefix condition, and strict increase of length.
    Every call terminates and uses only the original parameter. Pairing, tabulation, and each finite test
    have the stated beta/query reductions, so their composition returns exactly the required decision bit.
    \end{proof}
-/
theorem sectionForest_decidable {ε : ℕ → ℕ} (S : PairTree ε) :
    DecidablePredicate ε (fun z : ℕ => sectionForest S z.unpair.1 z.unpair.2) := by
  have hn := (projection_computes true).comp (projection_computes false)
  have hm := (projection_computes true).comp (projection_computes true)
  have hb := (projection_computes false).comp (projection_computes true)
  have ha := (projection_computes false).comp (projection_computes false)
  have he := (numerical_le_decidable hm hn ε).and (numerical_le_decidable hn hm ε)
  have ht := numericalSection_decidable S
  have hchild := ht.precompNumerical (hn.pair hb)
    (g := fun z : ℕ => Nat.pair z.unpair.2.unpair.1 z.unpair.1.unpair.2) (by simp)
  have hparent := ht.precompNumerical (projection_computes false)
    (g := fun z : ℕ => z.unpair.2) (by simp)
  have hp := word_prefix_decidable ha hb ε
  have hl := numerical_lt_decidable (listLength_computes.comp ha) (listLength_computes.comp hb) ε
  simpa only [sectionForest,RootedPrefixTree.codedExtension,Nat.unpair_pair,← le_antisymm_iff,ite_true,Bool.false_eq_true,ite_false] using
    he.and (hchild.and (hparent.and (hp.and hl)))

end LambdaTree
namespace RankBound

/-- Coding a disjoint family preserves the bounded-rank predicate in each component. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Bounded ranks in a coded forest
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induct along the bound relation, simultaneously for every word code. The bounded-rank recursion
    requires that each predecessor satisfy a lower bound. The predecessors of $\NatPair{n}{k}$ in $E$
    are exactly the pairs $\NatPair{n}{j}$ for which $s_j$ strictly extends $s_k$ inside $S_n$.
    Apply the induction hypothesis to each such predecessor. The two bounded-rank formulas therefore
    coincide at the current bound, including a bound with no predecessors.
    \end{proof}
-/
theorem holds_coded_family {β : Type} (R : β → β → Prop) (hR : WellFounded R)
    (E : ℕ → ℕ → ℕ → Prop) (a : β) (n s : ℕ) :
    Holds R hR (fun b c : ℕ => b.unpair.1 = c.unpair.1 ∧ E c.unpair.1 b.unpair.2 c.unpair.2)
      a (Nat.pair n s) ↔ Holds R hR (E n) a s := by
  induction a using hR.induction generalizing s with
  | h a ih =>
    rw [iff_children,iff_children]
    constructor
    · intro h t ht
      obtain ⟨b,hb,hbt⟩ := h (Nat.pair n t) (by simpa only [Nat.unpair_pair, true_and] using ht)
      exact ⟨b,hb,(ih b hb t).mp hbt⟩
    · intro h t ht
      simp only [Nat.unpair_pair] at ht
      obtain ⟨b,hb,hbt⟩ := h t.unpair.2 ht.2
      refine ⟨b,hb,?_⟩
      have he : t = Nat.pair n t.unpair.2 := by
        rw [← ht.1,Nat.pair_unpair]
      rw [he]
      exact (ih b hb t.unpair.2).mpr hbt

end RankBound
end PolishSpaceBook
