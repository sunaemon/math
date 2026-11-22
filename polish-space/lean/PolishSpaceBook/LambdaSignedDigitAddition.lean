module

public import PolishSpaceBook.LambdaSignedDigitSelection

@[expose] public section

/-! # Signed-digit addition by partial sums, averaging, and rational digit selection -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set Filter Topology

namespace NamedLambda.AlphaTerm
/-- Substitute a computed name into a program, preserving the numerical input. -/
theorem UniformNumericalComputes.name_comp {P Q : AlphaTerm}
    {f g : (ℕ → ℕ) → ℕ → ℕ} (hP : UniformNumericalComputes P f)
    (hQ : UniformNumericalComputes Q g) :
    UniformNumericalComputes (compositionProgram P Q) (fun p n => f (g p) n) :=
  ⟨compositionProgram_closed hP.1 hQ.1,fun p n =>
    compositionProgram_runs hP.1 hQ.1 (hP.2 (g p) n) (fun k => hQ.2 p k)⟩
end NamedLambda.AlphaTerm

noncomputable def unitIntervalAverage (x y : unitInterval) : unitInterval :=
  ⟨(x.val+y.val)/2,by constructor <;> linarith [x.property.1,x.property.2,y.property.1,y.property.2]⟩

noncomputable def unitIntervalSum (z : unitInterval × unitInterval) : Set.Icc (0:ℝ) 2 :=
  ⟨z.1.val+z.2.val,by constructor <;> linarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩

/-- The same digit alphabet, with its represented interval scaled from [0,1] to [0,2]. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For the output interval $\ClosedInterval{0}{2}$, use the scaled signed-digit representation
    $$\sigma_{\mathrm{sd}}(p):=2\rho_{\mathrm{sd}}(p).$$
    Its domain is the same set of coded signed-digit names. Scaling is surjective onto $\ClosedInterval{0}{2}$, so this is a
    representation of that interval.
-/
noncomputable def signedDigitSumRepresentation : Representation (Set.Icc (0:ℝ) 2) where
  domain := signedDigitNameDomain
  toFun p := ⟨2*(signedDigitRepresentation.toFun p).val,by
    constructor <;> linarith [(signedDigitRepresentation.toFun p).property.1,
      (signedDigitRepresentation.toFun p).property.2]⟩
  surjective := by
    intro x
    let y : unitInterval := ⟨x.val/2,by constructor <;> linarith [x.property.1,x.property.2]⟩
    obtain ⟨p,hp⟩ := signedDigitRepresentation.surjective y
    refine ⟨p,?_⟩
    apply Subtype.ext
    change 2*(signedDigitRepresentation.toFun p).val = x.val
    rw [hp]
    dsimp [y]
    ring

def signedAverageName (p q : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.pair (signedPartialNumerator p n+signedPartialNumerator q n) (n+2)

theorem signedAverageName_value (p q : signedDigitNameDomain) (n : ℕ) :
    (unitDyadicPoint (signedAverageName p.val q.val n)).val =
      (signedDigitPartialSum (decodeSignedDigits p) n+signedDigitPartialSum (decodeSignedDigits q) n)/2 := by
  have hp := (signedPartialNumerator_bounds p n).2
  have hq := (signedPartialNumerator_bounds q n).2
  have hb : signedPartialNumerator p.val n+signedPartialNumerator q.val n ≤ 2^(n+2) := by
    rw [show n+2=n+1+1 by omega,pow_succ]
    omega
  rw [signedAverageName,unitDyadicPoint_pair _ _ hb,← signedPartialNumerator_value,
    ← signedPartialNumerator_value]
  push_cast
  rw [show n+2=n+1+1 by omega,pow_succ]
  field_simp

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Let $p,q$ be signed-digit names of $x,y$. The forward translator above computes their partial sums
    $$s_n(p)=\frac{u_n(p)}{2^{n+1}},\qquad s_n(q)=\frac{u_n(q)}{2^{n+1}}.$$
    Use their common denominator to form a name for the average:
    $$\alpha(p,q)(n):=\NatPair{u_n(p)+u_n(q)}{n+2},\qquad
    \nu_{\alpha(p,q)(n)}=\frac{s_n(p)+s_n(q)}2.$$
    The numerator is less than $2^{n+2}$ because each $u_n(p)$ is less than $2^{n+1}$, so the dyadic enumeration
    returns exactly this average. For $n\le j$, the fast Cauchy estimates give
    $$\begin{aligned}
    \Abs{\nu_{\alpha(p,q)(n)}-\nu_{\alpha(p,q)(j)}}
    &\le\frac{\Abs{s_n(p)-s_j(p)}+\Abs{s_n(q)-s_j(q)}}{2}\\
    &\le\frac{2^{-n}+2^{-n}}2=2^{-n}.
    \end{aligned}$$
    Since the two partial sums converge to $x$ and $y$, the name $\alpha(p,q)$ represents $(x+y)/2$.
-/
theorem signedAverageName_isCauchy (p q : signedDigitNameDomain) :
    IsCauchyName unitDyadicPoint (signedAverageName p.val q.val) := by
  intro n m hnm
  change dist (unitDyadicPoint (signedAverageName p.val q.val n)).val
    (unitDyadicPoint (signedAverageName p.val q.val m)).val ≤ _
  rw [signedAverageName_value,signedAverageName_value,Real.dist_eq]
  have hp := signedDigitPartialSum_dist_le (decodeSignedDigits p) hnm
  have hq := signedDigitPartialSum_dist_le (decodeSignedDigits q) hnm
  rw [Real.dist_eq] at hp hq
  have he : ∀ a b c d : ℝ, (a+b)/2-(c+d)/2=((a-c)+(b-d))/2 := by intros; ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hs := abs_add_le
    (signedDigitPartialSum (decodeSignedDigits p) n-signedDigitPartialSum (decodeSignedDigits p) m)
    (signedDigitPartialSum (decodeSignedDigits q) n-signedDigitPartialSum (decodeSignedDigits q) m)
  linarith

theorem signedAverageName_limit (p q : signedDigitNameDomain) :
    cauchyRepresentation unitDyadicPoint ⟨signedAverageName p.val q.val,signedAverageName_isCauchy p q⟩ =
      unitIntervalAverage (signedDigitRepresentation.toFun p) (signedDigitRepresentation.toFun q) := by
  apply Subtype.ext
  have h := (continuous_subtype_val.tendsto _).comp (tendsto_cauchyRepresentation unitDyadicPoint
    ⟨signedAverageName p.val q.val,signedAverageName_isCauchy p q⟩)
  simp only [Function.comp_def,signedAverageName_value] at h
  exact tendsto_nhds_unique h
    (((tendsto_signedDigitPartialSum (decodeSignedDigits p)).add
      (tendsto_signedDigitPartialSum (decodeSignedDigits q))).div_const 2)

def signedInputProjectionProgram (left : Bool) : AlphaTerm :=
  mapOutputProgram (numericalProjectionTerm left) (queryOutputProgram (liftNumericalProgram numericalIdentity))

theorem signedInputProjectionProgram_computes (left : Bool) :
    UniformNumericalComputes (signedInputProjectionProgram left)
      (fun p n => if left then (p n).unpair.1 else (p n).unpair.2) :=
  numericalIdentity_computes.uniform.query.map (projection_computes left)

def signedAverageProgram : AlphaTerm :=
  pairOutputProgram
    (combineOutputProgram additionTerm
      (compositionProgram signedPartialNumeratorProgram (signedInputProjectionProgram true))
      (compositionProgram signedPartialNumeratorProgram (signedInputProjectionProgram false)))
    (liftNumericalProgram (numericalCombine additionTerm numericalIdentity (numericalConstant 2)))

theorem signedAverageProgram_computes : UniformNumericalComputes signedAverageProgram
    (fun p => signedAverageName (typeTwoLeftName p) (typeTwoRightName p)) := by
  have hL := signedPartialNumeratorProgram_computes.name_comp (signedInputProjectionProgram_computes true)
  have hR := signedPartialNumeratorProgram_computes.name_comp (signedInputProjectionProgram_computes false)
  have hI := numericalIdentity_computes.combine (numericalConstant_computes 2)
    additionTerm_closed (·+·) additionTerm_apply
  have h := (hL.combine hR additionTerm_closed (·+·) additionTerm_apply).pair hI.uniform
  refine ⟨h.1,fun p n => ?_⟩
  change OracleRuns p signedAverageProgram n
    (Nat.pair (signedPartialNumerator (fun k => (p k).unpair.1) n +
      signedPartialNumerator (fun k => (p k).unpair.2) n) (n+2))
  simpa only [signedAverageProgram,ite_true,Bool.false_eq_true,ite_false,id_eq] using h.2 p n

def signedAdditionProgram : AlphaTerm := compositionProgram cauchySignedNameProgram signedAverageProgram

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    To give one closed program, encode the input pair as $r:=\NamePair{p}{q}$ and set
    $$\LambdaTermName{input}_i:=\lambdaab{o}{\lambdaab{n}{\LambdaNumericProjection{i}(on)}}\qquad(i=1,2).$$
    Recall the numerator program $\LambdaTermName{signedNumerator}$ and the reverse translator
    $\LambdaTermName{cauchyToSigned}$ from the preceding proof. Define
    $$\begin{aligned}
    \LambdaTermName{sumNumerators}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaAdd\,( \LambdaTermName{signedNumerator}(
    \LambdaTermName{input}_1o)n)\,( \LambdaTermName{signedNumerator}( \LambdaTermName{input}_2o)n)}},\\
    \LambdaTermName{average}&:=\lambdaab{o}{\lambdaab{n}{\LambdaNumericPair\,(\LambdaTermName{sumNumerators}on)\,
    (\LambdaAdd\,n\,\ChurchNumeral{2})}},\\
    \LambdaTermName{addSigned}&:=\lambdaab{o}{\lambdaab{n}{\LambdaTermName{cauchyToSigned}(\LambdaTermName{average}o)n}}.
    \end{aligned}$$
    The projection terms supply the two input names to $\LambdaTermName{signedNumerator}$. Addition and pairing then
    make $\LambdaTermName{average}$ compute
    $\alpha(p,q)$. Substituting this computed name into $\LambdaTermName{cauchyToSigned}$ preserves every finite
    beta/query derivation by
    §{sec:lambda-input-composition}; each requested coordinate is answered by the corresponding finite
    computation of $\LambdaTermName{average}$. All variables are bound, and the value calculation above proves that
    $\LambdaTermName{addSigned}$ realizes addition.
-/
theorem signedAdditionProgram_computes : UniformNumericalComputes signedAdditionProgram
    (fun p => cauchySignedName (signedAverageName (typeTwoLeftName p) (typeTwoRightName p))) :=
  cauchySignedNameProgram_computes.name_comp signedAverageProgram_computes

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Let $\psi$ be the Cauchy-to-signed-digit translator just constructed. Its correctness gives
    $$\sigma_{\mathrm{sd}}(\psi(\alpha(p,q)))
    =2\rho_{\mathrm{sd}}(\psi(\alpha(p,q)))=2\frac{x+y}{2}=x+y.$$
    Thus the average is only an intermediate value: interpreting the output with $\sigma_{\mathrm{sd}}$ yields
    the required sum, including when it exceeds $1$.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Computable signed-digit addition
-/
theorem signedDigit_addition_computable : HasComputableRealizer
    (typeTwoProductRepresentation signedDigitRepresentation signedDigitRepresentation)
    signedDigitSumRepresentation unitIntervalSum := by
  let D := (typeTwoProductRepresentation signedDigitRepresentation signedDigitRepresentation).domain
  let F : D → signedDigitNameDomain := fun p =>
    cauchySignedNameValid (signedAverageName (typeTwoLeftName p.val) (typeTwoRightName p.val))
  refine ⟨F,⟨signedAdditionProgram,?_⟩,?_⟩
  · exact typeTwoComputes_iff_runs.mpr
      ⟨signedAdditionProgram_computes.1,fun p n => signedAdditionProgram_computes.2 p.val n⟩
  · intro p
    let l : signedDigitNameDomain := ⟨typeTwoLeftName p.val,p.property.1⟩
    let r : signedDigitNameDomain := ⟨typeTwoRightName p.val,p.property.2⟩
    let a : cauchyNameDomain unitDyadicPoint :=
      ⟨signedAverageName l.val r.val,signedAverageName_isCauchy l r⟩
    have hb : cauchyRepresentation (fun i => (unitDyadicPoint i).val)
        (intervalCauchyNameAsReal unitDyadicPoint a) ∈ Icc (0:ℝ) 1 := by
      rw [intervalCauchyNameAsReal_value]
      exact (cauchyRepresentation unitDyadicPoint a).property
    have hv := (cauchySignedDigits_value _ (intervalCauchyNameAsReal unitDyadicPoint a) hb).trans
      (intervalCauchyNameAsReal_value unitDyadicPoint a)
    change signedDigitExpansionValue (cauchySignedDigits (fun i => (unitDyadicPoint i).val) a.val) =
      (cauchyRepresentation unitDyadicPoint a).val at hv
    have ha := signedAverageName_limit l r
    change cauchyRepresentation unitDyadicPoint a = _ at ha
    apply Subtype.ext
    change 2*signedDigitExpansionValue (decodeSignedDigits (cauchySignedNameValid a.val)) =
      (signedDigitRepresentation.toFun l).val+(signedDigitRepresentation.toFun r).val
    rw [cauchySignedName_decode,hv,ha]
    dsimp [unitIntervalAverage]
    ring

end PolishSpaceBook
