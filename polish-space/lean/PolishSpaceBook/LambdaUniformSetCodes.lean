module

public import PolishSpaceBook.LambdaParameterizedOperations

@[expose] public section

/-! # Paired uniform presentations and finite-prefix atoms

The two presentations are constructed on every numerical input. Complementarity
is a separate property, so a compiler need not decide whether an input is valid.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance uniformSetListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance uniformSetPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

variable {ε : ℕ → ℕ}

/-- A finite-prefix predicate gives a uniform tree presentation at the original parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Uniform finite-prefix atom presentations
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let $\LambdaTermName{atomPredicate}$ decide the predicate and let $\LambdaTermName{boundProg}$ compute the
    bound. On numerical input
    $z=\NatPair{i}{\NatPair{\LambdaListCode{\sigma}}{\LambdaListCode{\tau}}}$, write
    $$\begin{aligned}
    \LambdaTermName{atomIndex}(z)&:=\LambdaNumericProjection{1}z,\\
    \LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{bound}(z)&:=\LambdaTermName{boundProg}(\LambdaTermName{atomIndex}(z)),\\
    \LambdaTermName{enoughPrefix}(z)&:= \LambdaLeCase{ \LambdaTermName{bound}(z)}{ \LambdaListLength\,
    \LambdaTermName{pointWord}(z)}{ \ChurchNumeral{1}}{ \ChurchNumeral{0}},\\
    \LambdaTermName{atomInput}(z)&:=\LambdaNumericPair\,\LambdaTermName{atomIndex}(z)\,
     (\LambdaListTake(\LambdaNumericPair\,\LambdaTermName{pointWord}(z)\,\LambdaTermName{bound}(z))).
    \end{aligned}$$
    With the bit negation $Z$ of §{sec:lambda-projection-programs}, use
    $$\LambdaTermName{atomTest}:= \lambdaab{o}{ \lambdaab{z}{Z( \LambdaMul\, \LambdaTermName{enoughPrefix}(z)\,(Z(
    \LambdaTermName{atomPredicate}o( \LambdaTermName{atomInput}(z)))))}}.$$
    Expand the abbreviations and choose fresh binders. This program decides
    $\nu(i)\le\Length{\sigma}\Rightarrow \Phi(i,\restrict{\sigma}{\nu(i)})$. Apply the finite-check-tree construction.
    On a branch, the test at length $\nu(i)$ forces the desired condition, and every later prefix tests
    the same word. Earlier prefixes impose no condition. The second branch coordinate is unrestricted,
    so the projection is exactly the required set. Replace the decision bit of the predicate by its
    negation to present the complement. All bounds, truncations, and decision calls are finite and total.
    The case of bound zero checks the empty prefix. A numerical guard independent of the point is
    obtained by ignoring the word and using bound zero.
-/
theorem uniform_prefix_atom {R : ℕ → List ℕ → Prop}
    (hR : LambdaRelative.DecidablePredicate ε (fun z : ℕ × List ℕ => R z.1 z.2))
    {B : AlphaTerm} {b : ℕ → ℕ} (hB : NumericalComputes B b) :
    UniformProjected ε (fun i => {x | R i (seqPrefix x (b i))}) := by
  have hi := projection_computes true
  have hw := computes_codeFirst (projection_computes false)
  have hb := hB.comp hi
  have ht := hR.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => (z.1,z.2.1.take (b z.1)))
    (hi.pair (listTake_computes.comp (hw.pair hb)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hg := (numerical_le_decidable hb (listLength_computes.comp hw) ε).precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => Encodable.encode z)
    numericalIdentity_computes (fun _ => rfl)
  have hj : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => b z.1 ≤ z.2.1.length → R z.1 (z.2.1.take (b z.1))) := by
    simpa [Encodable.encode,Encodable.encodeSigma] using hg.imp ht
  let T (i : ℕ) : PairTree ε := finiteCheckTree
    (fun z => b i ≤ z.1.length → R i (z.1.take (b i)))
    (hj.precompNumerical (g := fun z : List ℕ × List ℕ => (i,z))
      ((numericalConstant_computes i).pair numericalIdentity_computes)
      (fun z => by simp [Encodable.encode,Encodable.encodeSigma]))
  refine ⟨T,finiteCheck_family_decidable (test := fun i z => b i ≤ z.1.length → R i (z.1.take (b i))) hj,fun i => ?_⟩
  have hbody (x q : ℕ → ℕ) : (x,q) ∈ pairTreeBody (T i).tree ↔ R i (seqPrefix x (b i)) := by
    change (x,q) ∈ pairTreeBody (finiteCheckNodes
      (fun z => b i ≤ z.1.length → R i (z.1.take (b i)))) ↔ R i (seqPrefix x (b i))
    rw [pairTreeBody_finiteCheckNodes]
    simp only [seqPrefix_length]
    constructor
    · intro h
      simpa only [seqPrefix_take_of_le x le_rfl] using h (b i) le_rfl
    · intro h n hn
      simpa only [seqPrefix_take_of_le x hn] using h
  ext x
  constructor
  · intro hx; exact ⟨fun _ => 0,(hbody x _).mpr hx⟩
  · rintro ⟨q,hq⟩; exact (hbody x q).mp hq

/-- Positive and negative tree presentations; they need not be complementary on invalid inputs. -/
structure UniformSetPair (ε : ℕ → ℕ) where
  positive : ℕ → Set (ℕ → ℕ)
  negative : ℕ → Set (ℕ → ℕ)
  positive_uniform : UniformProjected ε positive
  negative_uniform : UniformProjected ε negative

namespace UniformSetPair

def CorrectAt (A : UniformSetPair ε) (i : ℕ) : Prop := A.negative i = (A.positive i)ᶜ

def swap (A : UniformSetPair ε) : UniformSetPair ε :=
  ⟨A.negative,A.positive,A.negative_uniform,A.positive_uniform⟩

def inter (A B : UniformSetPair ε) : UniformSetPair ε :=
  ⟨fun i => A.positive i ∩ B.positive i,fun i => A.negative i ∪ B.negative i,
   A.positive_uniform.inter B.positive_uniform,A.negative_uniform.union B.negative_uniform⟩

def union (A B : UniformSetPair ε) : UniformSetPair ε :=
  ⟨fun i => A.positive i ∪ B.positive i,fun i => A.negative i ∩ B.negative i,
   A.positive_uniform.union B.positive_uniform,A.negative_uniform.inter B.negative_uniform⟩

def reindex (A : UniformSetPair ε) {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) : UniformSetPair ε :=
  ⟨fun i => A.positive (f i),fun i => A.negative (f i),
   A.positive_uniform.reindex hF,A.negative_uniform.reindex hF⟩

def allNumbers (A : UniformSetPair ε) : UniformSetPair ε :=
  ⟨fun i => ⋂ k, A.positive (Nat.pair i k),fun i => ⋃ k, A.negative (Nat.pair i k),
   A.positive_uniform.iInterWithParameter,A.negative_uniform.iUnionWithParameter⟩

def someNumber (A : UniformSetPair ε) : UniformSetPair ε :=
  ⟨fun i => ⋃ k, A.positive (Nat.pair i k),fun i => ⋂ k, A.negative (Nat.pair i k),
   A.positive_uniform.iUnionWithParameter,A.negative_uniform.iInterWithParameter⟩

def prefixAtom {R : ℕ → List ℕ → Prop}
    (hR : LambdaRelative.DecidablePredicate ε (fun z : ℕ × List ℕ => R z.1 z.2))
    {B : AlphaTerm} {b : ℕ → ℕ} (hB : NumericalComputes B b) : UniformSetPair ε :=
  ⟨fun i => {x | R i (seqPrefix x (b i))},fun i => {x | ¬ R i (seqPrefix x (b i))},
   uniform_prefix_atom hR hB,uniform_prefix_atom (R := fun i s => ¬ R i s) hR.not hB⟩

def guard {R : ℕ → Prop} (hR : LambdaRelative.DecidablePredicate ε R) : UniformSetPair ε :=
  prefixAtom (R := fun i _ => R i) (hR.precompNumerical (g := fun z : ℕ × List ℕ => z.1)
    (projection_computes true) (fun z => by simp [Encodable.encode,Encodable.encodeSigma]))
    (numericalConstant_computes 0)

@[simp] theorem guard_positive {R : ℕ → Prop} (hR : LambdaRelative.DecidablePredicate ε R) (i x) :
    x ∈ (guard hR).positive i ↔ R i := Iff.rfl

@[simp] theorem guard_negative {R : ℕ → Prop} (hR : LambdaRelative.DecidablePredicate ε R) (i x) :
    x ∈ (guard hR).negative i ↔ ¬ R i := Iff.rfl

theorem correct_prefixAtom {R : ℕ → List ℕ → Prop}
    (hR : LambdaRelative.DecidablePredicate ε (fun z : ℕ × List ℕ => R z.1 z.2))
    {B : AlphaTerm} {b : ℕ → ℕ} (hB : NumericalComputes B b) (i) :
    (prefixAtom hR hB).CorrectAt i := rfl

theorem correct_guard {R : ℕ → Prop} (hR : LambdaRelative.DecidablePredicate ε R) (i) :
    (guard hR).CorrectAt i := rfl

theorem CorrectAt.swap {A : UniformSetPair ε} {i} (h : A.CorrectAt i) : A.swap.CorrectAt i := by
  simp only [CorrectAt,UniformSetPair.swap] at *
  rw [h,compl_compl]

theorem CorrectAt.inter {A B : UniformSetPair ε} {i}
    (hA : A.CorrectAt i) (hB : B.CorrectAt i) : (A.inter B).CorrectAt i := by
  simp only [CorrectAt,UniformSetPair.inter,compl_inter] at *
  rw [hA,hB]

theorem CorrectAt.union {A B : UniformSetPair ε} {i}
    (hA : A.CorrectAt i) (hB : B.CorrectAt i) : (A.union B).CorrectAt i := by
  simp only [CorrectAt,UniformSetPair.union,compl_union] at *
  rw [hA,hB]

theorem correct_reindex {A : UniformSetPair ε} {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) {i} (hA : A.CorrectAt (f i)) :
    (A.reindex hF).CorrectAt i := hA

theorem correct_allNumbers {A : UniformSetPair ε} {i}
    (hA : ∀ k, A.CorrectAt (Nat.pair i k)) : A.allNumbers.CorrectAt i := by
  simp only [CorrectAt,allNumbers,compl_iInter] at *
  simp only [hA]

theorem correct_someNumber {A : UniformSetPair ε} {i}
    (hA : ∀ k, A.CorrectAt (Nat.pair i k)) : A.someNumber.CorrectAt i := by
  simp only [CorrectAt,someNumber,compl_iUnion] at *
  simp only [hA]

theorem indices (A : UniformSetPair ε) :
    ∃ P N p n, NumericalComputes P p ∧ NumericalComputes N n ∧
      ∀ i, indexedProjection ε (p i) = A.positive i ∧
        indexedProjection ε (n i) = A.negative i := by
  obtain ⟨P,p,hP,hp⟩ := A.positive_uniform.indices
  obtain ⟨N,n,hN,hn⟩ := A.negative_uniform.indices
  exact ⟨P,N,p,n,hP,hN,fun i => ⟨hp i,hn i⟩⟩

end UniformSetPair
end LambdaTree
end PolishSpaceBook
