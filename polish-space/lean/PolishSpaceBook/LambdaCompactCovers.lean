module

public import PolishSpaceBook.CompactCoverCertificates
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # Closed lambda programs semideciding finite covers from computable finite nets -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set
universe u
variable {X : Type u} [MetricSpace X]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Compactness also has an effective strengthening. A compact space $K$ with a computable metric presentation is
    \termdefine{computably compact} if one closed numerical lambda program, on input $n$, returns a finite list
    $$E_n=(e_{n,0},\ldots,e_{n,\ell_n-1})$$
    of basic-point indices such that
    $$K=\bigcup_{k<\ell_n}\Ball{q_{e_{n,k}}}{2^{-n}}.$$
    The program returns the numerical list code from §{sec:lambda-finite-lists}. It is uniform in $n$.
-/
structure LambdaFiniteNets (q : ℕ → X) where
  centers : ℕ → List ℕ
  program : AlphaTerm
  computes : NumericalComputes program (fun n => NatListCode.encode (centers n))
  covers : IsDyadicNetSequence q centers

namespace NamedLambda.AlphaTerm

def numericalAllProgram (T N : AlphaTerm) : AlphaTerm :=
  numericalCompose (boundedProductTerm T) (pairNumerical numericalIdentity N)

theorem numericalAllProgram_computes {T N : AlphaTerm} {t n : ℕ → ℕ}
    (hT : NumericalComputes T t) (hN : NumericalComputes N n) :
    NumericalComputes (numericalAllProgram T N) (fun z => boundedProduct t z (n z)) := by
  have h := (boundedProduct_computes hT).comp (numericalIdentity_computes.pair hN)
  refine ⟨h.1,fun z => ?_⟩
  simpa only [numericalAllProgram,Nat.unpair_pair,id_eq] using h.2 z

def boundedAnyBit (t : ℕ → ℕ) (z N : ℕ) : ℕ :=
  if boundedProduct (fun w => if t w = 0 then 1 else 0) z N = 0 then 1 else 0

theorem boundedAnyBit_ne_zero (t : ℕ → ℕ) (z N : ℕ) :
    boundedAnyBit t z N ≠ 0 ↔ ∃ i < N, t (Nat.pair z i) ≠ 0 := by
  classical
  have ht : boundedProduct (fun w => if t w = 0 then 1 else 0) z N ≠ 0 ↔
      ∀ i < N, t (Nat.pair z i) = 0 := by
    rw [boundedProduct_ne_zero]
    simp
  have hz : boundedProduct (fun w => if t w = 0 then 1 else 0) z N = 0 ↔
      ∃ i < N, t (Nat.pair z i) ≠ 0 := by
    simpa only [ne_eq,not_not,not_forall,Classical.not_imp,exists_prop] using not_congr ht
  simp only [boundedAnyBit]
  split_ifs with h <;> simp_all

def numericalAnyProgram (T N : AlphaTerm) : AlphaTerm :=
  numericalCompose reverseZeroTerm (numericalAllProgram (numericalCompose reverseZeroTerm T) N)

theorem numericalAnyProgram_computes {T N : AlphaTerm} {t n : ℕ → ℕ}
    (hT : NumericalComputes T t) (hN : NumericalComputes N n) :
    NumericalComputes (numericalAnyProgram T N) (fun z => boundedAnyBit t z (n z)) :=
  reverseZero_computes.comp (numericalAllProgram_computes (reverseZero_computes.comp hT) hN)

end NamedLambda.AlphaTerm

def netPointBallBit {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (z : ℕ) : ℕ :=
  let b := z.unpair.1.unpair.1.unpair.1
  let n := z.unpair.1.unpair.1.unpair.2
  let i := z.unpair.1.unpair.2
  let j := z.unpair.2
  if (A.approx ((E n).getD i 0,(coverBallCenter b j,n))).value+2*(1/2:ℚ)^n <
      (coverBallRadius b j).value then 1 else 0

/-- Input codes ((ball list, stage), net position), followed by the ball position. -/
def netPointBallProgram (M N : AlphaTerm) : AlphaTerm :=
  let fst := numericalProjectionTerm true
  let snd := numericalProjectionTerm false
  let ctx := numericalCompose fst (numericalCompose fst fst)
  let stage := numericalCompose snd (numericalCompose fst fst)
  let ni := numericalCompose snd fst
  let point := numericalCompose listGetTerm (pairNumerical (numericalCompose N stage) ni)
  let ball := numericalCompose listGetTerm (pairNumerical ctx snd)
  let center := numericalCompose fst ball
  let radius := numericalCompose snd ball
  let approx := numericalCompose M (pairNumerical point (pairNumerical center stage))
  let error := numericalCompose rationalDyadicTerm stage
  let upper := numericalCompose rationalAddTerm (pairNumerical
    (numericalCompose rationalAddTerm (pairNumerical approx error)) error)
  numericalCompose rationalLessTerm (pairNumerical upper radius)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    We now construct the numerical program. Encode each ball by pairing its center index and rational radius
    code, and encode $B$ as a numerical list with code $b$. Let $C$ be the closed term that, on input
    $$\NatPair{\NatPair{\NatPair{b}{n}}{k}}{j},$$
    returns $1$ if the displayed rational inequality holds and $0$ otherwise. Numerical projections recover the
    indices; the finite-net program, $\LambdaListGet$, the distance program, rational addition, and rational comparison
    give $C$. Let $L$ compute $\ell_n$ from $z:=\NatPair{b}{n}$, and let $N$ compute $m$ from
    $w:=\NatPair{z}{k}$. These are closed terms obtained from projections, the net program, and $\LambdaListLength$.
-/
theorem netPointBallProgram_computes {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : NumericalComputes (netPointBallProgram A.program E.program)
      (netPointBallBit A.toRationalMetricApproximation E.centers) := by
  have f := projection_computes true
  have s := projection_computes false
  have ctx := f.comp (f.comp f)
  have stage := s.comp (f.comp f)
  have ni := s.comp f
  have point := listGet_computes.comp ((E.computes.comp stage).pair ni)
  have ball := listGet_computes.comp (ctx.pair s)
  have approx := A.computes.comp (point.pair ((f.comp ball).pair stage))
  have error := rationalDyadic_computes.comp stage
  have upper := rationalAdd_computes.comp ((rationalAdd_computes.comp (approx.pair error)).pair error)
  have h := rationalLess_computes.comp (upper.pair (s.comp ball))
  refine ⟨h.1,fun z => ?_⟩
  simpa only [netPointBallProgram,netPointBallBit,coverBallCenter,coverBallRadius,
    ite_true,Bool.false_eq_true,ite_false,Nat.unpair_pair,NatListCode.decode_encode,
    RationalCode.ofNat_natCode,RationalCode.value_add,RationalCode.value_dyadic,two_mul,add_assoc]
    using h.2 z

def netCoverRowBit {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (z : ℕ) : ℕ :=
  boundedAnyBit (netPointBallBit A E) z (NatListCode.decode z.unpair.1.unpair.1).length

def netCoverRowProgram (M N : AlphaTerm) : AlphaTerm :=
  numericalAnyProgram (netPointBallProgram M N) (numericalCompose listLengthTerm
    (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true)))

theorem netCoverRowProgram_computes {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : NumericalComputes (netCoverRowProgram A.program E.program)
      (netCoverRowBit A.toRationalMetricApproximation E.centers) := by
  have h := numericalAnyProgram_computes (netPointBallProgram_computes A E)
    (listLength_computes.comp ((projection_computes true).comp (projection_computes true)))
  refine ⟨h.1,fun z => ?_⟩
  simpa only [netCoverRowProgram,netCoverRowBit,ite_true] using h.2 z

def netCoverStageBit {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (z : ℕ) : ℕ := boundedProduct (netCoverRowBit A E) z (E z.unpair.2).length

def netCoverStageProgram (M N : AlphaTerm) : AlphaTerm :=
  numericalAllProgram (netCoverRowProgram M N)
    (numericalCompose listLengthTerm (numericalCompose N (numericalProjectionTerm false)))

theorem netCoverStageProgram_computes {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : NumericalComputes (netCoverStageProgram A.program E.program)
      (netCoverStageBit A.toRationalMetricApproximation E.centers) := by
  have h := numericalAllProgram_computes (netCoverRowProgram_computes A E)
    (listLength_computes.comp (E.computes.comp (projection_computes false)))
  refine ⟨h.1,fun z => ?_⟩
  simpa only [netCoverStageProgram,netCoverStageBit,Bool.false_eq_true,ite_false,NatListCode.decode_encode]
    using h.2 z

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Use the bounded-product terms from §{sec:lambda-prefix-margin-programs} and define
    $$\begin{aligned}
    Z&:=\lambdaab{v}{\LambdaZeroTest\,v\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    D&:=\lambdaab{u}{Z(Cu)},\\
    W&:=\lambdaab{w}{Z\bigl(\LambdaBoundedProduct{D}(\LambdaNumericPair\,w\,(Nw))\bigr)},\\
    T&:=\lambdaab{z}{\LambdaBoundedProduct{W}(\LambdaNumericPair\,z\,(Lz))}.
    \end{aligned}$$
    The inner product is nonzero exactly when every candidate ball fails for the chosen net point; applying $Z$
    therefore tests whether some ball succeeds. The outer product is nonzero exactly when this happens for every
    net point. Empty products have value $1$, so the same formulas also handle empty lists. Each bounded product
    terminates, and induction on its length verifies these assertions.
-/
theorem netCoverStageBit_ne_zero {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (b n : ℕ) :
    netCoverStageBit A E (Nat.pair b n) ≠ 0 ↔ netCoverCertificate A E b n := by
  simp only [netCoverStageBit,boundedProduct_ne_zero,Nat.unpair_pair,netCoverRowBit,
    boundedAnyBit_ne_zero,netPointBallBit,netCoverCertificate]
  simp

def netCoverSemidecider (M N : AlphaTerm) : AlphaTerm := numericalSearch (netCoverStageProgram M N)

theorem netCoverSemidecider_closed {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : (netCoverSemidecider A.program E.program).Closed :=
  numericalSearch_closed (netCoverStageProgram_computes A E).1

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Finally set
    $$I:=\lambdaab{x}{x},\qquad G_b:=\lambdaab{n}{Z(T(\LambdaNumericPair\,b\,n))},
    \qquad S:=\lambdaab{b}{\LambdaResultSearch\,G_b\,I}.$$
    The parameterized search in §{sec:lambda-rational-ball-programs} returns the first successful stage.
    When no stage succeeds, it has no numeral output under any reduction order. Thus $S$ is a single closed
    semidecider for all finite ball lists. The two metric arguments identify its domain with exactly the covering lists.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Finite-net cover semidecision
-/
theorem netCoverSemidecider_spec [CompactSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) (b : ℕ) :
    (∃ m, Relation.ReflTransGen Beta
      (app (netCoverSemidecider A.program E.program) (numeral b)) (numeral m)) ↔
        rationalBallListCovers q b := by
  rw [netCoverSemidecider,numericalSearch_domain (netCoverStageProgram_computes A E)]
  simp_rw [netCoverStageBit_ne_zero]
  exact (rationalBallListCovers_iff_certificate A.toRationalMetricApproximation E.covers b).symm

end PolishSpaceBook
