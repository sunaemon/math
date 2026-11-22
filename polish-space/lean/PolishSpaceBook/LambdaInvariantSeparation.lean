module

public import PolishSpaceBook.LambdaComplementedCodes
public import PolishSpaceBook.EquivalenceRelationSeparation

@[expose] public section

/-! # Invariant separation by numerical lambda recursion

The same fixed parameter supplies every stage and both complementary trees.
Only the set being avoided needs to be invariant.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance invariantListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance invariantPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Iterate a closed numerical program, using the numerical recursor with
an unused parameter and counter in its step body. -/
def numericalIterateTerm (a : ℕ) (N : AlphaTerm) : AlphaTerm :=
  numericalCompose (numericalRecursion (numericalConstant a)
    (numericalCompose N (codeSecond (numericalProjectionTerm false))))
    (pairNumerical (numericalConstant 0) numericalIdentity)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For invariant separation, let closed numerical programs $\LambdaTermName{separatorIndex},
    \LambdaTermName{complementIndex}, \LambdaTermName{saturationIndex}$ compute the separator index, its
    complementary index, and the saturation index. Fix input indices $a,b$. With distinct fresh binders,
    define the following terms, expanding all abbreviations before abstraction:
    $$\begin{aligned}
    \LambdaTermName{nextIndex}&:= \lambdaab{v}{ \LambdaTermName{saturationIndex}( \LambdaTermName{separatorIndex}(
    \LambdaNumericPair\,v\, \ChurchNumeral{b}))},\\
    \LambdaTermName{initialIndex}&:=\lambdaab{x}{\ChurchNumeral{a}},\\
    \LambdaTermName{previousInput}&:= \lambdaab{v}{ \LambdaTermName{nextIndex}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}v))},\\
    \LambdaTermName{iterationStep}&:= \lambdaab{x}{ \lambdaab{k}{ \lambdaab{r}{ \LambdaTermName{previousInput}(
    \LambdaNumericPair\,x\,( \LambdaNumericPair\,k\,r))}}},\\
    \LambdaTermName{iterate}&:= \lambdaab{n}{ \LambdaParamRec{ \LambdaTermName{initialIndex}}{
    \LambdaTermName{iterationStep}}\, \ChurchNumeral{0}\,n},\\
    \LambdaTermName{positiveStage}&:= \lambdaab{n}{ \LambdaTermName{separatorIndex}( \LambdaNumericPair\,(
    \LambdaTermName{iterate}n)\, \ChurchNumeral{b})},\\
    \LambdaTermName{negativeStage}&:= \lambdaab{n}{ \LambdaTermName{complementIndex}( \LambdaNumericPair\,(
    \LambdaTermName{iterate}n)\, \ChurchNumeral{b})}.
    \end{aligned}$$
    The two projections in $\LambdaTermName{previousInput}$ recover the previous value from the coded
    parameter-counter-value triple.
    Thus $\LambdaTermName{iterationStep}$ ignores the dummy parameter and counter and applies
    $\LambdaTermName{nextIndex}$ to that value. Numerical currying
    and uncurrying give these same computations when the recursor is implemented on paired inputs.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The numerical pairing and projection equations give $\LambdaTermName{iterationStep} \ChurchNumeral{0}\,
    \ChurchNumeral{k}\,
    \ChurchNumeral{r}\to_\beta^*\LambdaTermName{nextIndex}\ChurchNumeral{r}$. The initial value is $\ChurchNumeral{a}$.
    The parameterized recursor theorem therefore proves by induction that $\LambdaTermName{iterate}
    \ChurchNumeral{n}$ returns
    $\ChurchNumeral{a_n}$. Totality of $\LambdaTermName{separatorIndex}, \LambdaTermName{saturationIndex}$ gives
    termination at every successor stage. Composition gives
    the outputs of $\LambdaTermName{positiveStage}, \LambdaTermName{negativeStage}$, and reindexing the uniform tree
    decider by these terms gives the claimed joint
    family deciders. Invariance and disjointness are used in the set-theoretic proof of separation; neither
    is a condition that these programs test.
    \end{proof}
-/
theorem numericalIterate_computes (a : ℕ) {N : AlphaTerm} {next : ℕ → ℕ}
    (hN : NumericalComputes N next) :
    NumericalComputes (numericalIterateTerm a N) (primitiveRec a (fun _ i => next i)) := by
  have hh := hN.comp (computes_codeSecond (projection_computes false))
  have hr := (numericalRecursion_computes (numericalConstant_computes a) hh).comp
    ((numericalConstant_computes 0).pair numericalIdentity_computes)
  simpa only [numericalIterateTerm,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,id_eq] using hr

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    If $F$ and $A$ are lightface analytic, so is this saturation.
-/
theorem projected_erSaturation {ε : ℕ → ℕ} (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε E.r) {A : Set (ℕ → ℕ)} (hA : Projected ε A) :
    Projected ε (erSaturation E A) := projected_relationalImage hE hA

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Effective invariant separation
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    In this proof write $P_e$ for the uniform analytic presentations. Choose $a,b$ with $A=P_a$, $B=P_b$.
    Let $s,t$ be the separation-index transformations and let $h$ be the relational-image transformation for $F$.
    Define numerical indices by the recursion
    $$\begin{aligned}
    a_0&:=a,\\
    c_n&:=s(\NatPair{a_n}{b}),\qquad d_n:=t(\NatPair{a_n}{b}),\\
    a_{n+1}&:=h(c_n),\qquad A_n:=P_{a_n},\qquad C_n:=P_{c_n}.
    \end{aligned}$$
    Composition and the closed lambda recursor make $n\mapsto a_n,c_n,d_n$ total lambda-computable functions.
    The explicit terms are given in §{sec:lambda-lusin-image-programs}. Hence the trees for $C_n$ and $P_{d_n}$
    are jointly decidable in $n$ and their finite nodes.

    Inductively, $A_n$ is disjoint from $B$, separation gives
    $$A_n\IncludedIn C_n\IncludedIn B^{\complement},\qquad P_{d_n}=C_n^{\complement},$$
    and $A_{n+1}=\ERSaturation{C_n}{F}$. Indeed, a point of $B$ related to a point of $C_n$ would, by
    invariance of $B$, put that point of $C_n$ in $B$, a contradiction. Reflexivity gives
    $C_n\IncludedIn A_{n+1}$, so
    $$C:=\bigcup_n C_n=\bigcup_n A_n,\qquad C^{\complement}=\bigcap_n P_{d_n}.$$
    The uniform countable-operation constructions of §{sec:edst-uniform-countable-operations} give analytic
    presentations of both sides at the same parameter. Finally, if $x\in C_n$ and $x\mathrel F y$, then
    $y\in A_{n+1}\IncludedIn C_{n+1}$. Symmetry gives the reverse implication, so $C$ is invariant.
    It contains $A_0=A$, and every $C_n$ avoids $B$. This proves the conclusion; invariance of $A$ was not needed.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Programs for the invariant-separation stages
-/
theorem invariant_separation (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε E.r)
    {A B : Set (ℕ → ℕ)}
    (hA : Projected ε A)
    (hB : Projected ε B)
    (hAB : Disjoint A B) (hBinv : ERInvariant E B) :
    ∃ C, Complemented ε C ∧
      ERInvariant E C ∧ A ⊆ C ∧ Disjoint C B := by
  obtain ⟨a, rfl⟩ := (projected_iff_index ε A).mp hA
  obtain ⟨b, rfl⟩ := (projected_iff_index ε B).mp hB
  obtain ⟨sep, co, ⟨P,hsep⟩, ⟨Q,hco⟩, hseparates⟩ := exists_separationIndices ε
  obtain ⟨sat, ⟨S,hsat⟩, hsatEq⟩ := exists_relationalImageIndices ε E.r hE
  let next : ℕ → ℕ := fun i => sat (sep (Nat.pair i b))
  have hnext := hsat.comp (hsep.comp (numericalIdentity_computes.pair (numericalConstant_computes b)))
  let stage : ℕ → ℕ := primitiveRec a (fun _ i => next i)
  have hstage := numericalIterate_computes a hnext
  let ci : ℕ → ℕ := fun n => sep (Nat.pair (stage n) b)
  let ki : ℕ → ℕ := fun n => co (Nat.pair (stage n) b)
  let Cn : ℕ → Set (ℕ → ℕ) := fun n => indexedProjection ε (ci n)
  let Kn : ℕ → Set (ℕ → ℕ) := fun n => indexedProjection ε (ki n)
  have hstep (n : ℕ) : indexedProjection ε (stage (n + 1)) = erSaturation E (Cn n) :=
    hsatEq (sep (Nat.pair (stage n) b))
  have hdis (n : ℕ) : Disjoint (indexedProjection ε (stage n)) (indexedProjection ε b) := by
    induction n with
    | zero => exact hAB
    | succ n ih =>
      rw [hstep]
      exact erSaturation_disjoint E
        (Set.disjoint_left.mpr (fun x hx hxb => (hseparates (stage n) b ih).2.1 hx hxb)) hBinv
  have hsub (n : ℕ) : indexedProjection ε (stage n) ⊆ Cn n :=
    (hseparates (stage n) b (hdis n)).1
  have havoid (n : ℕ) : Cn n ⊆ (indexedProjection ε b)ᶜ :=
    (hseparates (stage n) b (hdis n)).2.1
  have hcompl (n : ℕ) : Kn n = (Cn n)ᶜ := by
    have h := (hseparates (stage n) b (hdis n)).2.2
    change Cn n = (Kn n)ᶜ at h
    rw [h, compl_compl]
  have hci := hsep.comp (hstage.pair (numericalConstant_computes b))
  have hki := hco.comp (hstage.pair (numericalConstant_computes b))
  have hcomplemented : Complemented ε (⋃ n, Cn n) :=
    complemented_uniform_iUnion
      (fun n => indexedTree ε (ci n)) (fun n => indexedTree ε (ki n))
      (indexedTree_reindex_decidable ε hci) (indexedTree_reindex_decidable ε hki) hcompl
  refine ⟨⋃ n, Cn n, hcomplemented, ?_, ?_, ?_⟩
  · intro x y hxy
    have hforward {x y : ℕ → ℕ} (hxy : E.r x y) (hx : x ∈ ⋃ n, Cn n) : y ∈ ⋃ n, Cn n := by
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      apply mem_iUnion.mpr
      refine ⟨n + 1, hsub (n + 1) ?_⟩
      rw [hstep]
      exact ⟨x, hn, hxy⟩
    exact ⟨hforward hxy, hforward (E.symm hxy)⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨0, hsub 0 hx⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact havoid n hn hxB

end LambdaTree
end PolishSpaceBook
