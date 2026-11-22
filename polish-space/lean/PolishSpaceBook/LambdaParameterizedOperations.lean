module

public import PolishSpaceBook.LambdaUniformFamilies

@[expose] public section

/-! # Countable operations retaining a numerical family parameter

The quantified index is carried in the witness; the outer index remains numerical
input to one finite-node decider. Specialization therefore computes output codes.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance parameterizedListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance parameterizedPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

variable {ε : ℕ → ℕ}

theorem unionTest_family_decidable (T : ℕ → ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => z.2.2 ∈ (T z.1 z.2.1).tree)) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => unionTest (fun k => (T z.1 k).tree) z.2) := by
  have ht := hT.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) =>
      (z.1,(z.2.2.getD 0 0,(z.2.1.take z.2.2.tail.length,z.2.2.tail))))
    ((projection_computes true).pair (unionInput_computes.comp (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hn := (nil_decidable ε).precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => z.2.2)
    (computes_codeSecond (projection_computes false))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  exact hn.or ht

theorem interTest_family_decidable (T : ℕ → ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => z.2.2 ∈ (T z.1 z.2.1).tree)) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => interTest (fun k => (T z.1 k).tree) z.2) := by
  -- The trial input is (((outer index,node),row),depth).
  have ha := computes_codeFirst (computes_codeFirst (projection_computes true))
  have hw := computes_codeSecond (computes_codeFirst (projection_computes true))
  have hi := computes_codeSecond (projection_computes true)
  have hk := projection_computes false
  have htrial := (hw.pair hi).pair hk
  have hc := hT.precompNumerical
    (g := fun z : ℕ => (z.unpair.1.unpair.1.unpair.1,
      (z.unpair.1.unpair.2,
       ((NatListCode.decode z.unpair.1.unpair.1.unpair.2.unpair.1).take z.unpair.2,
        witnessRow (NatListCode.decode z.unpair.1.unpair.1.unpair.2.unpair.2)
          z.unpair.1.unpair.2 z.unpair.2))))
    (ha.pair (interInput_computes.comp htrial))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hb : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      Nat.pair z.unpair.1.unpair.2 z.unpair.2 <
        (NatListCode.decode z.unpair.1.unpair.1.unpair.2.unpair.2).length) := by
    apply numericalDecision (interBound_computes.comp htrial) ε
    · intro z h; simp [h]
    · intro z h; simp [h]
  have hp := hb.imp hc
  have hinner := hp.boundedAll
    (listLength_computes.comp (computes_codeFirst (computes_codeSecond (projection_computes true))))
  have houter := hinner.boundedAll
    (listLength_computes.comp (computes_codeFirst (projection_computes false)))
  have h := houter.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => Encodable.encode z)
    numericalIdentity_computes (fun _ => rfl)
  simpa [interTest,Nat.unpair_pair,Encodable.encode,Encodable.encodeSigma,
    NatListCode.decode_encode,ite_true,Bool.false_eq_true,ite_false] using h

namespace UniformProjected
variable {A : ℕ → Set (ℕ → ℕ)}

theorem reindex (hA : UniformProjected ε A) {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) : UniformProjected ε (fun i => A (f i)) := by
  obtain ⟨T,hT,eT⟩ := hA
  refine ⟨fun i => T (f i), ?_, fun i => eT (f i)⟩
  exact hT.precompNumerical (g := fun z : ℕ × (List ℕ × List ℕ) => (f z.1,z.2))
    ((hF.comp (projection_computes true)).pair (projection_computes false))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Parameter-preserving countable tree operations
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let $P$ be the joint decider, with numerical input coding the triple consisting of the outer index,
    the quantified index, and the node. Retain the outer index by using the template
    $$P_a:=\lambdaab{o}{\lambdaab{w}{Po(\LambdaNumericPair\,a\,w)}}.$$
    Here $w$ codes the quantified index and node. Insert this template into the union and intersection
    programs of §{sec:lambda-projection-programs}, expanding its body and choosing fresh binders.
    For a joint output decider, extract $a$ and the node from its numerical input and retain $a$
    through both bounded products and every finite-prefix test. In the union construction the witness
    head selects a component; in the intersection construction its paired positions supply all component
    witnesses. Thus the previous body identities hold at every fixed $a$, while all finite tests remain
    jointly decidable. Numerical specialization of these two fixed joint programs computes the required
    indices. It does not search for an infinite witness or test nonemptiness. Apply the intersection
    construction to the input complements to obtain the complement of the union, and the union
    construction to obtain the complement of the intersection.
-/
theorem iUnionWithParameter (hA : UniformProjected ε A) :
    UniformProjected ε (fun i => ⋃ k, A (Nat.pair i k)) := by
  obtain ⟨T,hT,eT⟩ := hA
  have hj := hT.precompNumerical
    (g := fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => (Nat.pair z.1 z.2.1,z.2.2))
    (((projection_computes true).pair (computes_codeFirst (projection_computes false))).pair
      (computes_codeSecond (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hs (i : ℕ) := hj.precompNumerical (g := fun z : ℕ × (List ℕ × List ℕ) => (i,z))
    ((numericalConstant_computes i).pair numericalIdentity_computes)
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  refine ⟨fun i => unionTree (fun k => T (Nat.pair i k)) (hs i),
    finiteCheck_family_decidable (test := fun i => unionTest (fun k => (T (Nat.pair i k)).tree))
      (unionTest_family_decidable (fun i k => T (Nat.pair i k)) hj), ?_⟩
  intro i
  simp only [pairTreeProjection_unionTree,eT]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Parameter-preserving countable tree operations
-/
theorem iInterWithParameter (hA : UniformProjected ε A) :
    UniformProjected ε (fun i => ⋂ k, A (Nat.pair i k)) := by
  obtain ⟨T,hT,eT⟩ := hA
  have hj := hT.precompNumerical
    (g := fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => (Nat.pair z.1 z.2.1,z.2.2))
    (((projection_computes true).pair (computes_codeFirst (projection_computes false))).pair
      (computes_codeSecond (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hs (i : ℕ) := hj.precompNumerical (g := fun z : ℕ × (List ℕ × List ℕ) => (i,z))
    ((numericalConstant_computes i).pair numericalIdentity_computes)
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  refine ⟨fun i => interTree (fun k => T (Nat.pair i k)) (hs i),
    finiteCheck_family_decidable (test := fun i => interTest (fun k => (T (Nat.pair i k)).tree))
      (interTest_family_decidable (fun i k => T (Nat.pair i k)) hj), ?_⟩
  intro i
  simp only [pairTreeProjection_interTree,eT]

/-- Extract numerical codes from the joint finite-node decider, not from
pointwise choices of a presentation. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Parameter-preserving countable tree operations
-/
theorem indices (hA : UniformProjected ε A) :
    ∃ F f, NumericalComputes F f ∧ ∀ i, indexedProjection ε (f i) = A i := by
  obtain ⟨T,hT,eT⟩ := hA
  obtain ⟨f,⟨F,hF⟩,hf⟩ := treeFamily_indices ε T hT
  exact ⟨F,f,hF,fun i => (pairTreeProjection_indexedTree ε (f i) (T i).tree (hf i)).trans (eT i).symm⟩

theorem complemented_countableWithParameter
    (hA : UniformProjected ε A) (hAc : UniformProjected ε (fun i => (A i)ᶜ)) :
    UniformProjected ε (fun i => ⋃ k, A (Nat.pair i k)) ∧
    UniformProjected ε (fun i => (⋃ k, A (Nat.pair i k))ᶜ) ∧
    UniformProjected ε (fun i => ⋂ k, A (Nat.pair i k)) ∧
    UniformProjected ε (fun i => (⋂ k, A (Nat.pair i k))ᶜ) := by
  refine ⟨hA.iUnionWithParameter, ?_, hA.iInterWithParameter, ?_⟩
  · simpa only [compl_iUnion] using hAc.iInterWithParameter
  · simpa only [compl_iInter] using hAc.iUnionWithParameter

end UniformProjected
end LambdaTree
end PolishSpaceBook
