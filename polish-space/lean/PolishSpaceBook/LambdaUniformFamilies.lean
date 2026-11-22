module

public import PolishSpaceBook.LambdaComplementedCodes

@[expose] public section

/-! # Uniform projected families with joint lambda deciders -/

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance uniformListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance uniformPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable
variable {ε : ℕ → ℕ}

/-- A single lambda program decides membership jointly in index and node. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Fix a parameter $\varepsilon$. For a sequence of relative pair trees $T_i$, require one closed lambda
    program deciding $(s,t)\in T_i$ with $i,s,t$ as inputs and parameter $\varepsilon$.
-/
def UniformProjected (ε : ℕ → ℕ) (A : ℕ → Set (ℕ → ℕ)) : Prop :=
  ∃ T : ℕ → PairTree ε,
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree) ∧
    ∀ n, A n = pairTreeProjection (T n).tree

namespace UniformProjected
variable {A B : ℕ → Set (ℕ → ℕ)}

theorem const {D : Set (ℕ → ℕ)} (hD : Projected ε D) :
    UniformProjected ε (fun _ => D) := by
  obtain ⟨T, hT⟩ := hD
  exact ⟨fun _ => T, constantTree_family_decidable T, fun _ => hT⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{uniform analytic kernel tests}{Uniform analytic kernel tests}]
-/
theorem inter (hA : UniformProjected ε A) (hB : UniformProjected ε B) :
    UniformProjected ε (fun n => A n ∩ B n) := by
  obtain ⟨T, hT, eT⟩ := hA
  obtain ⟨S, hS, eS⟩ := hB
  exact ⟨fun n => (T n).intersection (S n), intersection_family_decidable T S hT hS,
    fun n => by simp only [eT, eS, pairTreeProjection_intersection]⟩

theorem coordinatePreimage (hA : UniformProjected ε A) {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) :
    UniformProjected ε (fun n => {x | (fun k => f (x k)) ∈ A n}) := by
  obtain ⟨T,hT,eT⟩ := hA
  exact ⟨fun n => (T n).coordinatePreimage hF,
    coordinatePreimage_family_decidable T hT hF,
    fun n => by simpa only [eT,Set.preimage,Function.comp_def] using (pairTreeProjection_coordinatePreimage (T n) hF).symm⟩

theorem left (hA : UniformProjected ε A) :
    UniformProjected ε (fun n => {x | leftBaire x ∈ A n}) :=
  hA.coordinatePreimage (projection_computes true)

theorem right (hA : UniformProjected ε A) :
    UniformProjected ε (fun n => {x | rightBaire x ∈ A n}) :=
  hA.coordinatePreimage (projection_computes false)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{uniform analytic kernel tests}{Uniform analytic kernel tests}]
-/
theorem nonempty (hA : UniformProjected ε A) :
    UniformProjected ε (fun n => {_x | (A n).Nonempty}) := by
  obtain ⟨T, hT, eT⟩ := hA
  exact ⟨fun n => (T n).nonemptiness, nonemptiness_family_decidable T hT,
    fun n => by simp only [eT, pairTreeProjection_nonemptiness]⟩

/-- The witness head chooses a side; the family index remains ordinary input. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Retain the family index through each word transformation using the wrapper of
    §{sec:lambda-lusin-image-programs}. For intersections, split the witness into two coordinates and run both
    deciders. For a binary union, the first witness entry selects the first tree when zero and the second
    otherwise; apply the union construction of §{sec:edst-uniform-countable-operations} while retaining
    the family index. For nonemptiness, use $N(T_e)$ from the preceding proof. Finally, the uniform
    intersection construction stores one witness row for each index and checks finitely many guarded
    entries at each stage. These operations compute only finite tree tests; they do not decide whether
    a projected set is empty.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the binary union of two jointly decidable families, let $\LambdaTermName{leftFamily},
    \LambdaTermName{rightFamily}$ be their closed decision programs.
    Write $z=\NatPair{i}{\NatPair{k}{w}}$, with these letters abbreviating numerical projections in the
    following bodies. Let $Z$ be the numerical zero test from §{sec:lambda-projection-programs},
    and put
    $$\begin{aligned}
    \LambdaTermName{firstChoice}(z)&:=Zk,\qquad \LambdaTermName{familyInput}(z):=\LambdaNumericPair\,i\,w,\\
    \LambdaTermName{leftBit}(o,z)&:= \LambdaMul\, \LambdaTermName{firstChoice}(z)\,( \LambdaTermName{leftFamily}o(
    \LambdaTermName{familyInput}(z))),\\
    \LambdaTermName{rightBit}(o,z)&:= \LambdaMul\,(Z( \LambdaTermName{firstChoice}(z)))\,(
    \LambdaTermName{rightFamily}o( \LambdaTermName{familyInput}(z))),\\
    \LambdaTermName{unionRow}&:= \lambdaab{o}{ \lambdaab{z}{Z( \LambdaMul\,(Z( \LambdaTermName{leftBit}(o,z)))\,(Z(
    \LambdaTermName{rightBit}(o,z))))}}.
    \end{aligned}$$
    On numerical input this returns the decision for the first family when $k=0$ and for the second
    otherwise. Both supplied deciders terminate, so evaluating both branches causes no difficulty.
    Next retain $i$ while applying the union input transformation $K_U$ to the node code $w$, and run
    $\LambdaTermName{unionRow}$ on the resulting triple. Take the Boolean disjunction with the test that the witness
    word is empty,
    then apply the finite-test construction. Its body uses the head of the witness to select a family and
    its tail as the selected witness. This gives a joint tree decider for the binary union, including empty
    trees. Together with the index-retaining intersection, projection, and nonemptiness programs, it
    supplies every family operation in the Silver and HKL kernel tests.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{uniform analytic kernel tests}{Uniform analytic kernel tests}]
-/
theorem union (hA : UniformProjected ε A) (hB : UniformProjected ε B) :
    UniformProjected ε (fun n => A n ∪ B n) := by
  obtain ⟨T,hT,eT⟩ := hA
  obtain ⟨S,hS,eS⟩ := hB
  let R (n k : ℕ) := if k = 0 then T n else S n
  have hzero : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => z.2.1 = 0) := by
    apply numericalDecision
      (reverseZero_computes.comp (computes_codeFirst (projection_computes false))) ε
    · intro z h; simp [Encodable.encode,Encodable.encodeSigma,h]
    · intro z h; simp [Encodable.encode,Encodable.encodeSigma,h]
  have ht := hT.precompNumerical
    (g := fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => (z.1,z.2.2))
    ((projection_computes true).pair (computes_codeSecond (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hs := hS.precompNumerical
    (g := fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => (z.1,z.2.2))
    ((projection_computes true).pair (computes_codeSecond (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hj : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (ℕ × (List ℕ × List ℕ)) => z.2.2 ∈ (R z.1 z.2.1).tree) := by
    convert (hzero.and ht).or (hzero.not.and hs) using 1
    funext z
    apply propext
    simp only [R]; split_ifs <;> simp_all
  have hr (n : ℕ) : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (R n z.1).tree) :=
    hj.precompNumerical (g := fun z => (n,z))
      ((numericalConstant_computes n).pair numericalIdentity_computes)
      (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hinput := hj.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) =>
      (z.1,(z.2.2.getD 0 0,(z.2.1.take z.2.2.tail.length,z.2.2.tail))))
    ((projection_computes true).pair (unionInput_computes.comp (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hnil := (nil_decidable ε).precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => z.2.2)
    (computes_codeSecond (projection_computes false))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  refine ⟨fun n => unionTree (R n) (hr n),
    finiteCheck_family_decidable (test := fun n => unionTest (fun k => (R n k).tree))
      (hnil.or hinput), ?_⟩
  intro n
  rw [pairTreeProjection_unionTree]
  ext x
  simp only [mem_union,mem_iUnion]
  constructor
  · rintro (h | h)
    · exact ⟨0,by simpa [R,← eT] using h⟩
    · exact ⟨1,by simpa [R,← eS] using h⟩
  · rintro ⟨k,hk⟩
    by_cases h : k = 0
    · exact Or.inl (by simpa [R,h,← eT] using hk)
    · exact Or.inr (by simpa [R,h,← eS] using hk)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{uniform analytic kernel tests}{Uniform analytic kernel tests}]
-/
theorem iInter (hA : UniformProjected ε A) : Projected ε (⋂ n, A n) := by
  obtain ⟨T, hT, eT⟩ := hA
  simpa only [eT] using projected_uniform_iInter T hT

end UniformProjected

namespace ComplementedCodes
variable {ε : ℕ → ℕ} (C : ComplementedCodes ε)

theorem uniform_positive : UniformProjected ε C.positiveSet :=
  ⟨fun n => indexedTree ε (C.positive n),C.positive_family_decidable,fun _ => rfl⟩

theorem uniform_negative : UniformProjected ε C.negativeSet :=
  ⟨fun n => indexedTree ε (C.negative n),C.negative_family_decidable,fun _ => rfl⟩

end ComplementedCodes

theorem uniform_invalidComplementedIndex (ε : ℕ → ℕ) :
    UniformProjected ε (fun n => {_x | ¬ ValidComplementedIndex ε n}) :=
  ⟨invalidComplementedTree ε,invalidComplementedTree_family_decidable ε,
    fun n => (pairTreeProjection_invalidComplementedTree ε n).symm⟩

end LambdaTree
end PolishSpaceBook
