module

public import PolishSpaceBook.LambdaCoverFamilies
public import PolishSpaceBook.LambdaMetricPreimages

@[expose] public section

/-! # Semideciding finite ambient-ball covers of a computable image

Merge the preimage enumerations of the candidate balls, preserving the list code
as a numerical parameter. The source's coverage semidecider then gives an exact
semidecider for coverage of the image, including exclusion of false outputs.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

def imagePreimageEntry (e : ℕ → ℕ) (z : ℕ) : ℕ :=
  if z.unpair.2.unpair.1 < (NatListCode.decode z.unpair.1).length then
    e (Nat.pair ((NatListCode.decode z.unpair.1).getD z.unpair.2.unpair.1 0) z.unpair.2.unpair.2)
  else 0

def imagePreimageProgram (E : AlphaTerm) : AlphaTerm :=
  let b := numericalProjectionTerm true
  let j := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let k := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  let guard := numericalCombine strictLessTerm j (numericalCompose listLengthTerm b)
  let ball := numericalCompose listGetTerm (pairNumerical b j)
  mulNumerical guard (numericalCompose E (pairNumerical ball k))

theorem imagePreimageProgram_computes {E : AlphaTerm} {e : ℕ → ℕ} (he : NumericalComputes E e) :
    NumericalComputes (imagePreimageProgram E) (imagePreimageEntry e) := by
  have hb := projection_computes true
  have hj := (projection_computes true).comp (projection_computes false)
  have hk := (projection_computes false).comp (projection_computes false)
  have guard := hj.combine (listLength_computes.comp hb) strictLessTerm_closed
    (fun a b => if a < b then 1 else 0) strictLessTerm_apply
  have ball := listGet_computes.comp (hb.pair hj)
  have h := guard.mul (he.comp (ball.pair hk))
  refine ⟨h.1,fun z => ?_⟩
  simpa [imagePreimageProgram,imagePreimageEntry,ite_mul] using h.2 z

def imageBallListCovers (q : ℕ → Y) (f : X → Y) (b : ℕ) : Prop :=
  ∀ x, ∃ j < (NatListCode.decode b).length,
    dist (f x) (q (coverBallCenter b j)) < (coverBallRadius b j).value

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The effective inverse-image criterion in §{sec:tte-polish-as-represented} supplies a closed numerical term $F$
    computing $e(c,k)$, an enumeration of the preimage of the target ball coded by $c$. For an input list
    $C=(c_j)_{j<\ell}$ with code $b$, merge these enumerations by pairing the ball position and its enumeration stage:
    $$\widehat e(b,\NatPair{j}{k}):=
    \begin{cases}e(c_j,k),&j<\ell,\\0,&j\ge\ell.\end{cases}$$
    Write $V(v)$ for the source ball represented by enumeration value $v$, with $V(0)=\varnothing$, and $W(c)$ for
    the target ball coded by $c$. Then
    $$\bigcup_t V(\widehat e(b,t))
    =f^{-1}\!\left(\bigcup_{j<\ell}W(c_j)\right).$$
    Indeed, a nonempty emitted source ball belongs to one of the preimage enumerations, and every stage of every
    listed ball occurs at its paired index. Hence the merged enumeration covers $K$ exactly when the target balls
    cover $f[K]$. This also handles the empty list: all merged stages are then empty.
-/
theorem imagePreimageEntry_cover_iff {qX : ℕ → X} {qY : ℕ → Y} {f : X → Y} {e : ℕ → ℕ}
    (he : ∀ b, (⋃ k, enumeratedRationalBall qX (e (Nat.pair b k))) =
      f ⁻¹' Metric.ball (qY b.unpair.1) ((RationalCode.ofNat b.unpair.2).value:ℝ)) (b : ℕ) :
    IsEnumeratedCover qX (fun k => imagePreimageEntry e (Nat.pair b k)) ↔
      imageBallListCovers qY f b := by
  constructor
  · intro h x
    obtain ⟨k,hk⟩ := h x
    simp only [imagePreimageEntry,Nat.unpair_pair] at hk
    split_ifs at hk with hj
    · have hx : x ∈ ⋃ t, enumeratedRationalBall qX
          (e (Nat.pair ((NatListCode.decode b).getD k.unpair.1 0) t)) := mem_iUnion.mpr ⟨_,hk⟩
      rw [he] at hx
      exact ⟨k.unpair.1,hj,hx⟩
    · simp [enumeratedRationalBall] at hk
  · intro h x
    obtain ⟨j,hj,hx⟩ := h x
    have hx' : x ∈ f ⁻¹' Metric.ball (qY ((NatListCode.decode b).getD j 0).unpair.1)
        ((RationalCode.ofNat ((NatListCode.decode b).getD j 0).unpair.2).value:ℝ) := hx
    rw [← he] at hx'
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx'
    refine ⟨Nat.pair j k,?_⟩
    simpa [imagePreimageEntry,hj] using hk

def imageCoverSemidecider (M N E : AlphaTerm) : AlphaTerm :=
  coverFamilySemidecider M N (imagePreimageProgram E)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Here is the numerical program for the merge. On input $z=\NatPair{b}{\NatPair{j}{k}}$, projections compute
    $j$ and $k$; $\LambdaListLength$ computes $\ell$, and $\LambdaListGet$ extracts $c_j$ when $j<\ell$.
    Let $J,Q,B$ be the closed terms computing these three extracted values, with zero-default list access outside
    the list, and let $A$ be the closed numerical comparison term returning $1$ when $j<\ell$ and $0$ otherwise.
    Then
    $$F_{\cup}:=\lambdaab{z}{\LambdaMul\,(Az)\,
     \bigl(F(\LambdaNumericPair\,(Bz)\,(Qz))\bigr)}$$
    computes $\widehat e$. Every component is total; even when $j\ge\ell$, the enumeration term returns a number,
    and multiplication by zero suppresses it. Apply the uniform coverage lemma to $F_{\cup}$. Its semidecider has a
    numeral output exactly when the displayed preimage is all of $K$, which is exactly the desired finite-cover relation.
    The program depends on the fixed metric, finite-net and preimage-enumeration programs, while the candidate list
    remains its numerical input.
    \end{proof}
-/
theorem imageCoverSemidecider_spec [CompactSpace X] {qX : ℕ → X} {qY : ℕ → Y} {f : X → Y}
    (A : LambdaMetricApproximation qX) (N : LambdaFiniteNets qX)
    {E : AlphaTerm} {e : ℕ → ℕ} (hE : NumericalComputes E e)
    (he : ∀ b, (⋃ k, enumeratedRationalBall qX (e (Nat.pair b k))) =
      f ⁻¹' Metric.ball (qY b.unpair.1) ((RationalCode.ofNat b.unpair.2).value:ℝ)) (b : ℕ) :
    (∃ m, Relation.ReflTransGen Beta
      (app (imageCoverSemidecider A.program N.program E) (numeral b)) (numeral m)) ↔
        imageBallListCovers qY f b := by
  rw [imageCoverSemidecider,coverFamilySemidecider_spec A N (imagePreimageProgram_computes hE)]
  exact imagePreimageEntry_cover_iff he b

theorem image_has_coverSemidecider [CompactSpace X] {qX : ℕ → X} {qY : ℕ → Y} {f : X → Y}
    (A : LambdaMetricApproximation qX) (N : LambdaFiniteNets qX)
    (hf : HasEnumerableBallPreimages qX qY f) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ b,
      (∃ m, Relation.ReflTransGen Beta (app P (numeral b)) (numeral m)) ↔
        imageBallListCovers qY f b := by
  obtain ⟨E,e,hE,he⟩ := hf
  exact ⟨imageCoverSemidecider A.program N.program E,
    coverFamilySemidecider_closed A N (imagePreimageProgram_computes hE),
    imageCoverSemidecider_spec A N hE he⟩

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Finite covers of a computable image
-/
theorem computable_image_has_coverSemidecider [CompactSpace X] [CompleteSpace X] [CompleteSpace Y]
    {qX : ℕ → X} {qY : ℕ → Y} (A : LambdaMetricApproximation qX) (B : LambdaMetricApproximation qY)
    (N : LambdaFiniteNets qX) (hqX : DenseRange qX) (hqY : DenseRange qY) (f : X → Y)
    (hf : HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ b,
      (∃ m, Relation.ReflTransGen Beta (app P (numeral b)) (numeral m)) ↔
        imageBallListCovers qY f b :=
  image_has_coverSemidecider A N (A.enumerableBallPreimages_of_realizer B hqX hqY f hf)

end PolishSpaceBook
