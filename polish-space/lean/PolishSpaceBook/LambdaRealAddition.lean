module

public import PolishSpaceBook.LambdaAssemblyProducts
public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaNumericalQueries

@[expose] public section

/-! # Addition of Cauchy reals and its assembly tracker -/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm Filter Topology

def realSumName (p q : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((RationalCode.ofNat (p (n+1))).add (RationalCode.ofNat (q (n+1)))).natCode

@[simp] theorem realSumName_value (p q : ℕ → ℕ) (n : ℕ) :
    rationalPoint (realSumName p q n) = rationalPoint (p (n+1)) + rationalPoint (q (n+1)) := by
  simp [realSumName,rationalPoint]

theorem realSumName_isCauchy (p q : realRepresentation.domain) :
    IsCauchyName rationalPoint (realSumName p.val q.val) := by
  intro n m hnm
  rw [realSumName_value,realSumName_value]
  calc
    _ ≤ dist (rationalPoint (p.val (n+1))) (rationalPoint (p.val (m+1))) +
        dist (rationalPoint (q.val (n+1))) (rationalPoint (q.val (m+1))) := dist_add_add_le _ _ _ _
    _ ≤ (1/2:ℝ)^(n+1)+(1/2:ℝ)^(n+1) :=
      add_le_add (p.property _ _ (by omega)) (q.property _ _ (by omega))
    _ = _ := by ring

theorem realSumName_limit (p q : realRepresentation.domain) :
    realRepresentation.toFun ⟨realSumName p.val q.val,realSumName_isCauchy p q⟩ =
      realRepresentation.toFun p + realRepresentation.toFun q := by
  have hp := (tendsto_cauchyRepresentation rationalPoint p).comp (Filter.tendsto_add_atTop_nat 1)
  have hq := (tendsto_cauchyRepresentation rationalPoint q).comp (Filter.tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint
    ⟨realSumName p.val q.val,realSumName_isCauchy p q⟩)
  simpa only [Function.comp_def,realSumName_value,realRepresentation,cauchyRepresentationObject] using hp.add hq

/-- Query the paired input once at n+1 and add the two rational codes. -/
def realAdditionProgram : AlphaTerm :=
  mapOutputProgram rationalAddTerm (queryOutputProgram (liftNumericalProgram successorTerm))

theorem realAdditionProgram_computes : UniformNumericalComputes realAdditionProgram
    (fun r => realSumName (typeTwoLeftName r) (typeTwoRightName r)) := by
  exact successor_computes.uniform.query.map rationalAdd_computes

theorem addition_hasComputableRealizer : HasComputableRealizer
    (typeTwoProductRepresentation realRepresentation realRepresentation)
    realRepresentation (fun z => z.1+z.2) := by
  let F : (typeTwoProductRepresentation realRepresentation realRepresentation).domain →
      realRepresentation.domain := fun p =>
    ⟨realSumName (typeTwoLeftName p.val) (typeTwoRightName p.val),
      realSumName_isCauchy ⟨_,p.property.1⟩ ⟨_,p.property.2⟩⟩
  refine ⟨F,⟨realAdditionProgram,?_⟩,?_⟩
  · exact typeTwoComputes_iff_runs.mpr
      ⟨realAdditionProgram_computes.1,fun p n => realAdditionProgram_computes.2 p.val n⟩
  · intro p
    exact realSumName_limit ⟨_,p.property.1⟩ ⟨_,p.property.2⟩

/-- The domain is the product of the two assemblies, not merely a paired-name encoding. -/
noncomputable def realAdditionMap : Assembly.Hom
    (Assembly.prod (computablePointAssembly realRepresentation) (computablePointAssembly realRepresentation))
    (computablePointAssembly realRepresentation) :=
  (computablePointPair realRepresentation realRepresentation).comp
    (computablePointMap addition_hasComputableRealizer)

@[simp] theorem realAdditionMap_value (x y : (computablePointAssembly realRepresentation).Carrier) :
    (realAdditionMap.toFun (x,y)).val = x.val+y.val := rfl

/-- One total syntax transformer accepts a numerical pair of name indices. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Tracked addition
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $p_1,p_2$ be Cauchy names of $x,y$. Using the rational addition program of
    §{sec:lambda-rational-arithmetic}, define $a(p_1,p_2)(n)$ to be a code for
    $$q_{a(p_1,p_2)(n)}=q_{p_1(n+1)}+q_{p_2(n+1)}.$$
    For $m\ge n$, the two input bounds give
    $$\begin{aligned}
    |q_{a(p_1,p_2)(n)}-q_{a(p_1,p_2)(m)}|
    &\le |q_{p_1(n+1)}-q_{p_1(m+1)}|
       +|q_{p_2(n+1)}-q_{p_2(m+1)}|\\
    &\le 2^{-(n+1)}+2^{-(n+1)}=2^{-n}.
    \end{aligned}$$
    Both summands converge to their respective represented reals. Thus $a(p_1,p_2)$ is a valid Cauchy name of $x+y$;
    the one-coordinate shift supplies exactly the required precision.
    For a paired input name $r=\NamePair{p_1}{p_2}$, the following closed terms implement the construction:
    $$\begin{aligned}
    S&:=\lambdaab{o}{\LambdaSucc},\\
    Q&:=\lambdaab{o}{\lambdaab{n}{o(Son)}},\\
    P&:=\lambdaab{o}{\lambdaab{n}{\LambdaRationalAdd(Qon)}}.
    \end{aligned}$$
    The first term computes the successor independently of the supplied name. The second queries $r(n+1)$, which is
    already the numerical pair of the two rational codes. The third adds those coded rationals. Beta contraction,
    one name query, and the terminating rational computation prove that $P$ produces $a(p_1,p_2)$ at every
    coordinate.
    Now let $s$ be the pairing-index function and let $t$ be the name-to-index transformation for $P$. The composite
    $z\mapsto t(s(z))$ is total and lambda-computable on every numerical input. On $z=\NatPair{e}{f}$ realizing
    $(x,y)$, it returns an index for $a(\varphi_e,\varphi_f)$, hence a realizer of $x+y$. This is a tracker on
    $A\times A$. The assembly embedding and its product calculation above then give the asserted morphism in
    $\EffCat$.
    \end{proof}
-/
theorem addition_indices : ∃ t : ℕ → ℕ, (∃ k, ∀ z, App k z (t z)) ∧
    ∀ (x y : (computablePointAssembly realRepresentation).Carrier) e f,
      e ∈ (computablePointAssembly realRepresentation).realizes x →
      f ∈ (computablePointAssembly realRepresentation).realizes y →
      t (Nat.pair e f) ∈ (computablePointAssembly realRepresentation).realizes
        (realAdditionMap.toFun (x,y)) := by
  obtain ⟨s,⟨ks,hks⟩,hs⟩ := pairName_indices
  obtain ⟨F,⟨P,hP⟩,hF⟩ := addition_hasComputableRealizer
  obtain ⟨t,⟨kt,hkt⟩,ht⟩ := typeTwo_index_transform hP
  have hc := (ComputesName.eval hkt).comp (ComputesName.eval hks)
  obtain ⟨k,hk⟩ := Term.closedProgram_surjective _ hc.1
  refine ⟨fun z => t (s z),⟨k,fun z => ?_⟩,?_⟩
  · unfold App
    rw [hk]
    exact hc.2 z
  · rintro x y e f ⟨p,hp,he⟩ ⟨q,hq,hf⟩
    let r : (typeTwoProductRepresentation realRepresentation realRepresentation).domain :=
      ⟨typeTwoPairName p.val q.val,by
        change typeTwoLeftName (typeTwoPairName p.val q.val) ∈ realRepresentation.domain ∧
          typeTwoRightName (typeTwoPairName p.val q.val) ∈ realRepresentation.domain
        simpa only [typeTwoLeft_pair,typeTwoRight_pair] using And.intro p.property q.property⟩
    refine ⟨F r,?_,ht r _ (hs e f p.val q.val he hf)⟩
    have hr : (typeTwoProductRepresentation realRepresentation realRepresentation).toFun r =
        (x.val,y.val) := by
      apply Prod.ext
      · simpa [r,typeTwoProductRepresentation] using hp
      · simpa [r,typeTwoProductRepresentation] using hq
    exact (hF r).trans (congrArg (fun z : ℝ × ℝ => z.1+z.2) hr)

/-- The tracked map also yields an arrow between the corresponding realizability PERs. -/
noncomputable def realAdditionRelation : FunctionalRelation
    (RealizerPER.product (computablePointAssembly realRepresentation).toPER
      (computablePointAssembly realRepresentation).toPER)
    (computablePointAssembly realRepresentation).toPER := by
  rw [← Assembly.prod_toPER]
  exact realAdditionMap.toRelation

end PolishSpaceBook.LambdaIndexPCA
