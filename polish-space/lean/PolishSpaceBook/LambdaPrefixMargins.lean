module

public import PolishSpaceBook.LambdaDistanceRelations
public import PolishSpaceBook.LambdaListAccess
public import PolishSpaceBook.LambdaBoundedProducts
public import PolishSpaceBook.CauchyPrefixMargins

@[expose] public section

/-! # Total lambda tests for finitely many Cauchy margins

The numerical input is `pair listCode (pair center (pair radiusExponent precision))`.
A bounded product checks exactly the entries of the decoded list. Empty prefixes
are accepted. The metric lemmas prove soundness and availability of these
certificates independently of the semideciding program.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm
set_option maxHeartbeats 800000

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply this bounded product to Cauchy margins. Suppose a closed term $M$ returns the rational code $A(u,i,k)$ from the
    numerical input $\NatPair{u}{\NatPair{i}{k}}$. Encode the finite data by
    $$w:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}}.$$
    On input $\NatPair{w}{n}$, projections recover the list code and all four indices. In the following term expressions,
    $e,i,\ell,k,n$ abbreviate those projection terms. Form
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(\LambdaListGet\,(\LambdaNumericPair\,e\,n))
           (\LambdaNumericPair\,i\,k)),\\
    E&:=\LambdaDyadic\,k,\qquad R:=\LambdaDyadic\,\ell,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,R),\\
    D&:=\LambdaDyadic\,(\LambdaSucc\,n).
    \end{aligned}$$
    Composition gives a closed stage term $T_M$ whose body reduces to $\LambdaRationalLess\,(\LambdaNumericPair\,U\,D)$.
    Finally put
    $$\LambdaPrefixMargins{M}:=\lambdaab{w}{\LambdaBoundedProduct{T_M}\,
     (\LambdaNumericPair\,w\,(\LambdaListLength\,(\LambdaNumericProjection{1}w)))}.$$
-/
def prefixMarginStage (M : AlphaTerm) : AlphaTerm :=
  let W := numericalProjectionTerm true
  let N := numericalProjectionTerm false
  let S := firstOutput W
  let I := firstOutput (secondOutput W)
  let L := firstOutput (secondOutput (secondOutput W))
  let K := secondOutput (secondOutput (secondOutput W))
  let V := numericalCompose M (pairNumerical
    (numericalCompose listGetTerm (pairNumerical S N)) (pairNumerical I K))
  let E := numericalCompose rationalDyadicTerm K
  let R := numericalCompose rationalDyadicTerm L
  let B := numericalCompose rationalDyadicTerm (numericalCompose successorTerm N)
  numericalCompose rationalLessTerm (pairNumerical
    (numericalCompose rationalAddTerm (pairNumerical
      (numericalCompose rationalAddTerm (pairNumerical V E)) R)) B)

def prefixMarginStageValue (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) : ℕ :=
  let w := z.unpair.1
  let s := NatListCode.decode w.unpair.1
  let i := w.unpair.2.unpair.1
  let l := w.unpair.2.unpair.2.unpair.1
  let k := w.unpair.2.unpair.2.unpair.2
  let n := z.unpair.2
  if (approx (s.getD n 0,(i,k))).value + (1/2 : ℚ)^k + (1/2 : ℚ)^l < (1/2 : ℚ)^(n+1)
    then 1 else 0

theorem prefixMarginStage_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    NumericalComputes (prefixMarginStage M) (prefixMarginStageValue approx) := by
  have hw := projection_computes true
  have hn := projection_computes false
  have hs := hw.first
  have hi := hw.second.first
  have hl := hw.second.second.first
  have hk := hw.second.second.second
  have hv := hM.comp ((listGet_computes.comp (hs.pair hn)).pair (hi.pair hk))
  have he := rationalDyadic_computes.comp hk
  have hr := rationalDyadic_computes.comp hl
  have hb := rationalDyadic_computes.comp (successor_computes.comp hn)
  have hsum := rationalAdd_computes.comp ((rationalAdd_computes.comp (hv.pair he)).pair hr)
  unfold prefixMarginStageValue
  simpa [prefixMarginStage,Nat.unpair_pair] using rationalLess_computes.comp (hsum.pair hb)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply this bounded product to Cauchy margins. Suppose a closed term $M$ returns the rational code $A(u,i,k)$ from the
    numerical input $\NatPair{u}{\NatPair{i}{k}}$. Encode the finite data by
    $$w:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}}.$$
    On input $\NatPair{w}{n}$, projections recover the list code and all four indices. In the following term expressions,
    $e,i,\ell,k,n$ abbreviate those projection terms. Form
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(\LambdaListGet\,(\LambdaNumericPair\,e\,n))
           (\LambdaNumericPair\,i\,k)),\\
    E&:=\LambdaDyadic\,k,\qquad R:=\LambdaDyadic\,\ell,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,R),\\
    D&:=\LambdaDyadic\,(\LambdaSucc\,n).
    \end{aligned}$$
    Composition gives a closed stage term $T_M$ whose body reduces to $\LambdaRationalLess\,(\LambdaNumericPair\,U\,D)$.
    Finally put
    $$\LambdaPrefixMargins{M}:=\lambdaab{w}{\LambdaBoundedProduct{T_M}\,
     (\LambdaNumericPair\,w\,(\LambdaListLength\,(\LambdaNumericProjection{1}w)))}.$$
-/
def allPrefixMarginsProgram (M : AlphaTerm) := numericalCompose (boundedProductTerm (prefixMarginStage M))
  (pairNumerical numericalIdentity (numericalCompose listLengthTerm (numericalProjectionTerm true)))

def allPrefixMarginsValue (approx : ℕ × (ℕ × ℕ) → RationalCode) (w : ℕ) : ℕ :=
  boundedProduct (prefixMarginStageValue approx) w (NatListCode.decode w.unpair.1).length

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact finite margin program
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: lemma
  title: Total finite Cauchy-margin test
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    List access gives the entry $s(n)$ whenever $n<|s|$. The supplied term computes its distance-approximation code; the
    dyadic terms and two additions give the left side of the inequality. Successor and dyadic coding give the right side.
    Rational comparison returns the correct zero-or-one value. The length term computes the exact number of entries, and the
    bounded-product lemma tests precisely those indices. Every ingredient is total and closed, so their composition has the
    stated properties, including the empty-prefix case.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The finite-list programs compute $\Length{s}$ and read each $s(n)$. Numerical projections, the supplied approximation
    term and
    rational arithmetic decide each displayed inequality as a zero-or-one value $t_n$. Starting with $z_0=1$, use numerical
    primitive recursion to set $z_{n+1}=z_nt_n$ for $n<\Length{s}$. The resulting value is one exactly when every test
    succeeds;
    the empty product is one. All component calculations terminate, so the whole test is total. The constructions and
    reductions are given in §{sec:lambda-prefix-margin-programs}.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply this bounded product to Cauchy margins. Suppose a closed term $M$ returns the rational code $A(u,i,k)$ from the
    numerical input $\NatPair{u}{\NatPair{i}{k}}$. Encode the finite data by
    $$w:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}}.$$
    On input $\NatPair{w}{n}$, projections recover the list code and all four indices. In the following term expressions,
    $e,i,\ell,k,n$ abbreviate those projection terms. Form
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(\LambdaListGet\,(\LambdaNumericPair\,e\,n))
           (\LambdaNumericPair\,i\,k)),\\
    E&:=\LambdaDyadic\,k,\qquad R:=\LambdaDyadic\,\ell,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,R),\\
    D&:=\LambdaDyadic\,(\LambdaSucc\,n).
    \end{aligned}$$
    Composition gives a closed stage term $T_M$ whose body reduces to $\LambdaRationalLess\,(\LambdaNumericPair\,U\,D)$.
    Finally put
    $$\LambdaPrefixMargins{M}:=\lambdaab{w}{\LambdaBoundedProduct{T_M}\,
     (\LambdaNumericPair\,w\,(\LambdaListLength\,(\LambdaNumericProjection{1}w)))}.$$
-/
theorem allPrefixMarginsProgram_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    NumericalComputes (allPrefixMarginsProgram M) (allPrefixMarginsValue approx) := by
  have h := (boundedProduct_computes (prefixMarginStage_computes approx hM)).comp
    (numericalIdentity_computes.pair (listLength_computes.comp (projection_computes true)))
  unfold allPrefixMarginsValue
  simpa [allPrefixMarginsProgram,Nat.unpair_pair] using h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact finite margin program
-/
theorem allPrefixMarginsValue_success (approx : ℕ × (ℕ × ℕ) → RationalCode) (w : ℕ) :
    allPrefixMarginsValue approx w ≠ 0 ↔
      ∀ n < (NatListCode.decode w.unpair.1).length,
        (approx ((NatListCode.decode w.unpair.1).getD n 0,
          (w.unpair.2.unpair.1,w.unpair.2.unpair.2.unpair.2))).value +
          (1/2 : ℚ)^w.unpair.2.unpair.2.unpair.2 + (1/2 : ℚ)^w.unpair.2.unpair.2.unpair.1 <
            (1/2 : ℚ)^(n+1) := by
  simp [allPrefixMarginsValue,boundedProduct_ne_zero,prefixMarginStageValue,Nat.unpair_pair]

theorem allPrefixMarginsValue_zero_or_one (approx : ℕ × (ℕ × ℕ) → RationalCode) (w : ℕ) :
    allPrefixMarginsValue approx w = 0 ∨ allPrefixMarginsValue approx w = 1 := by
  apply boundedProduct_zero_or_one
  intro n
  dsimp only [prefixMarginStageValue]
  split_ifs <;> simp

theorem allPrefixMarginsValue_empty (approx : ℕ × (ℕ × ℕ) → RationalCode) (i l k : ℕ) :
    allPrefixMarginsValue approx (Nat.pair 0 (Nat.pair i (Nat.pair l k))) = 1 := by
  simp [allPrefixMarginsValue,boundedProduct,primitiveRec,NatListCode.decode]

end NamedLambda.AlphaTerm

namespace LambdaMetricApproximation
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)

theorem prefixMargins_sound (w : ℕ) (hw : allPrefixMarginsValue A.approx w ≠ 0) :
    ∀ n < (NatListCode.decode w.unpair.1).length,
      dist (q ((NatListCode.decode w.unpair.1).getD n 0)) (q w.unpair.2.unpair.1) +
        (1/2 : ℝ)^w.unpair.2.unpair.2.unpair.1 < (1/2 : ℝ)^(n+1) := by
  intro n hn
  have ht := (allPrefixMarginsValue_success A.approx w).mp hw n hn
  have ht := (Rat.cast_lt (K := ℝ)).mpr ht
  push_cast at ht
  have herr := (abs_le.mp (A.error ((NatListCode.decode w.unpair.1).getD n 0)
    w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2)).1
  linarith

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: lemma
  title: Total finite Cauchy-margin test
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    On success, the distance error bound gives $d(q_{s(n)},q_i)+2^{-\ell}<2^{-(n+1)}$ for every $n<\Length{s}$. Apply the
    Cauchy-prefix margin lemma to each point of the ball. This last step is geometric: it supplies a valid extension,
    without computing a name for an arbitrary point of the ball.
    \end{proof}
-/
theorem prefixMargins_ball_extends [CompleteSpace X] (hq : DenseRange q) (w : ℕ)
    (hw : allPrefixMarginsValue A.approx w ≠ 0) {x : X}
    (hx : x ∈ Metric.ball (q w.unpair.2.unpair.1) ((1/2 : ℝ)^w.unpair.2.unpair.2.unpair.1)) :
    ∃ p : cauchyNameDomain q, p.val ∈ cyl (NatListCode.decode w.unpair.1) ∧
      cauchyRepresentation q p = x :=
  ball_extends_cauchyPrefix hq _ _ _ (A.prefixMargins_sound w hw) hx

/-- Every finite prefix of a strict dense name admits one of the tested balls. -/
theorem exists_prefixMargins (hq : DenseRange q) (p : ℕ → ℕ) (x : X)
    (hp : ∀ n, dist (q (p n)) x < (1/2 : ℝ)^(n+1)) (N : ℕ) :
    ∃ i l, allPrefixMarginsValue A.approx
      (Nat.pair (NatListCode.encode (seqPrefix p N)) (Nat.pair i (Nat.pair l l))) ≠ 0 ∧
      x ∈ Metric.ball (q i) ((1/2 : ℝ)^l) := by
  obtain ⟨l,hl⟩ := exists_dyadic_prefix_margin p x hp N
  obtain ⟨i,hi⟩ := hq.exists_dist_lt x (by positivity : 0 < (1/2 : ℝ)^l)
  refine ⟨i,l,?_,hi⟩
  apply (allPrefixMarginsValue_success A.approx _).mpr
  simp only [Nat.unpair_pair,NatListCode.decode_encode,seqPrefix_length]
  intro n hn
  have hget : (seqPrefix p N).getD n 0 = p n := by simp [seqPrefix,hn]
  rw [hget]
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  have herr := (abs_le.mp (A.error (p n) i l)).2
  have htri := dist_triangle (q (p n)) x (q i)
  have hi' : dist x (q i) < (1/2 : ℝ)^l := hi
  linarith [hl n hn]

end LambdaMetricApproximation
end PolishSpaceBook
