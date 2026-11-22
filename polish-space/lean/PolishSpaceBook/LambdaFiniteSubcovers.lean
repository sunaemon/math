module

public import PolishSpaceBook.LambdaCompactCovers
public import PolishSpaceBook.LambdaEffectiveBallEnumeration
public import PolishSpaceBook.LambdaNameRecursion

@[expose] public section

/-! # A finite subcover computed uniformly from an enumerated cover

The enumeration is supplied as an input name, not as a fixed computable sequence.
Search pairs of prefix length and net precision using total finite tests.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set
universe u
variable {X : Type u} [MetricSpace X]

def enumeratedCoverPrefix (p : ℕ → ℕ) (m : ℕ) : ℕ :=
  NatListCode.encode ((List.range m).map (fun i => p i - 1))

theorem enumeratedRationalBall_pred (q : ℕ → X) (v : ℕ) :
    enumeratedRationalBall q v = Metric.ball (q (v-1).unpair.1)
      ((RationalCode.ofNat (v-1).unpair.2).value:ℝ) := by
  cases v with
  | zero => simp [enumeratedRationalBall,RationalCode.ofNat,RationalCode.value]
  | succ v => simp [enumeratedRationalBall]

theorem enumeratedCoverPrefix_covers (q : ℕ → X) (p : ℕ → ℕ) (m : ℕ) :
    rationalBallListCovers q (enumeratedCoverPrefix p m) ↔
      ∀ x, ∃ i < m, x ∈ enumeratedRationalBall q (p i) := by
  simp only [rationalBallListCovers,enumeratedCoverPrefix,NatListCode.decode_encode,
    List.length_map,List.length_range,coverBallCenter,coverBallRadius]
  have he (i : ℕ) (hi : i < m) :
      ((List.range m).map (fun i => p i - 1)).getD i 0 = p i - 1 := by
    simp [List.getD,hi]
  constructor <;> intro h x <;> obtain ⟨i,hi,hx⟩ := h x <;> refine ⟨i,hi,?_⟩
  · simpa only [he i hi,enumeratedRationalBall_pred,Metric.mem_ball] using hx
  · simpa only [he i hi,enumeratedRationalBall_pred,Metric.mem_ball] using hx

def IsEnumeratedCover (q : ℕ → X) (p : ℕ → ℕ) : Prop :=
  ∀ x, ∃ i, x ∈ enumeratedRationalBall q (p i)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $V_i$ for the set at enumeration stage $i$. Each $V_i$ is open, including the empty stages.
    The cover $K=\bigcup_i V_i$ has a finite subcover by compactness. A number $m$ larger than its indices then satisfies
    $$K=\bigcup_{i<m}V_i.$$
    This proves existence of a covering prefix. To find one, we will search pairs of prefix lengths and net precisions.
-/
theorem enumeratedCover_has_prefix [CompactSpace X] (q : ℕ → X) {p : ℕ → ℕ}
    (hp : IsEnumeratedCover q p) : ∃ m, rationalBallListCovers q (enumeratedCoverPrefix p m) := by
  have hc : (univ : Set X) ⊆ ⋃ i, enumeratedRationalBall q (p i) := by
    intro x _; exact mem_iUnion.mpr (hp x)
  have ho (i : ℕ) : IsOpen (enumeratedRationalBall q (p i)) := by
    rw [enumeratedRationalBall_pred]; exact Metric.isOpen_ball
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover _ ho hc
  refine ⟨s.sup id+1,(enumeratedCoverPrefix_covers q p _).mpr ?_⟩
  intro x
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
  exact ⟨i,Nat.lt_succ_of_le (Finset.le_sup (f := id) his),hxi⟩

def coverPrefixStepProgram : AlphaTerm :=
  combineOutputProgram listAppendTerm (liftNumericalProgram (numericalProjectionTerm false))
    (combineOutputProgram listConsTerm
      (mapOutputProgram predecessorTerm
        (queryOutputProgram (liftNumericalProgram (numericalProjectionTerm true))))
      (constantProgram 0))

theorem coverPrefixStepProgram_computes : UniformNumericalComputes coverPrefixStepProgram
    (fun p z => NatListCode.encode (NatListCode.decode z.unpair.2 ++ [p z.unpair.1-1])) := by
  have hv := (projection_computes true).uniform.query.map predecessor_computes
  have hlist := hv.combine (uniform_constant 0) listConsTerm_closed
    (fun a d => Nat.pair a d+1) listConsTerm_apply
  have h := (projection_computes false).uniform.combine hlist listAppendTerm_closed
    (fun a b => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode b)) listAppendTerm_apply
  refine ⟨h.1,fun p z => ?_⟩
  simpa [coverPrefixStepProgram,NatListCode.decode] using h.2 p z

def coverPrefixProgram : AlphaTerm := nameRecursionProgram 0 coverPrefixStepProgram

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Turn enumeration entries into raw ball codes by
    $$d(v):=\begin{cases}0,&v=0,\\v-1,&v>0.\end{cases}$$
    The raw code $0$ denotes the ball of radius zero at $q_0$, which is empty. Thus this conversion preserves every
    stage's set. Let $b_p(m)$ code the list $(d(p(i)))_{i<m}$. The predecessor term computes $d$, and the following
    recursion computes this list from the supplied name:
    $$\begin{aligned}
    B&:=\lambdaab{o}{\ChurchNumeral{0}},\\
    H&:=\lambdaab{o}{\lambdaab{k}{\lambdaab{r}{
     \LambdaListAppend\,r\,(\LambdaListCons\,(\LambdaPred(ok))\,\ChurchNumeral{0})}}},\\
    L&:=\LambdaParamRec{B}{H}.
    \end{aligned}$$
    The initial value is the empty-list code. Each update queries $p(k)$ and appends its converted code.
    Induction on $m$ gives $Lo\ChurchNumeral{m}\to^*\ChurchNumeral{b_p(m)}$ by beta reductions and input queries.
    Only the first $m$ enumeration entries are read.
-/
theorem coverPrefixProgram_computes : UniformNumericalComputes coverPrefixProgram enumeratedCoverPrefix := by
  have h := coverPrefixStepProgram_computes.recursion 0
  have hv (p : ℕ → ℕ) (m : ℕ) :
      primitiveRec 0 (fun k r => NatListCode.encode (NatListCode.decode r ++ [p k-1])) m =
        enumeratedCoverPrefix p m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [primitiveRec,ih]
      simp only [enumeratedCoverPrefix,NatListCode.decode_encode,List.range_succ,
        List.map_append,List.map_cons,List.map_nil]
  refine ⟨h.1,fun p n => ?_⟩
  simpa only [coverPrefixProgram,Nat.unpair_pair,hv] using h.2 p n

def subcoverStageBit {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (p : ℕ → ℕ) (k : ℕ) : ℕ :=
  netCoverStageBit A E (Nat.pair (enumeratedCoverPrefix p k.unpair.1) k.unpair.2)

def subcoverStageProgram (M N : AlphaTerm) : AlphaTerm :=
  mapOutputProgram (netCoverStageProgram M N)
    (pairOutputProgram (reindexProgram coverPrefixProgram (numericalProjectionTerm true))
      (liftNumericalProgram (numericalProjectionTerm false)))

theorem subcoverStageProgram_computes {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : UniformNumericalComputes (subcoverStageProgram A.program E.program)
      (subcoverStageBit A.toRationalMetricApproximation E.centers) :=
  ((coverPrefixProgram_computes.reindex (projection_computes true)).pair
    (projection_computes false).uniform).map (netCoverStageProgram_computes A E)

theorem subcoverStageBit_sound {q : ℕ → X} (A : RationalMetricApproximation q)
    {E : ℕ → List ℕ} (hE : IsDyadicNetSequence q E) (p : ℕ → ℕ) {k : ℕ}
    (hk : subcoverStageBit A E p k ≠ 0) :
    ∀ x, ∃ i < k.unpair.1, x ∈ enumeratedRationalBall q (p i) := by
  exact (enumeratedCoverPrefix_covers q p _).mp
    (netCoverCertificate_sound A hE ((netCoverStageBit_ne_zero A E _ _).mp hk))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Let $T$ be the total finite-net test constructed above. On input $\NatPair{b}{n}$ it returns a nonzero numeral
    exactly when the ball list coded by $b$ passes the rational margin test at precision $n$. Define
    $$D:=\lambdaab{o}{\lambdaab{k}{T(\LambdaNumericPair\,
     (Lo(\LambdaNumericProjection{1}k))\,(\LambdaNumericProjection{2}k))}}.$$
    For $k=\NatPair{m}{n}$, the test $Dok$ first computes $b_p(m)$ and then tests that prefix at precision $n$.
    Every such test terminates. A successful test certifies that the prefix covers $K$, by the finite-net lemma.
    Conversely, a covering prefix exists by compactness, and that lemma supplies a precision at which it passes.
    Hence some paired candidate succeeds. Enumerating pairs prevents a noncovering prefix from blocking the search.
-/
theorem subcoverStageBit_exists [CompactSpace X] {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) {p : ℕ → ℕ} (hp : IsEnumeratedCover q p) :
    ∃ k, subcoverStageBit A E p k ≠ 0 := by
  obtain ⟨m,hm⟩ := enumeratedCover_has_prefix q hp
  obtain ⟨n,hn⟩ := netCoverCertificate_complete A E hm
  refine ⟨Nat.pair m n,?_⟩
  simpa only [subcoverStageBit,Nat.unpair_pair,netCoverStageBit_ne_zero] using hn

namespace NamedLambda.AlphaTerm

/-- Adapt a test on a name and candidate to search's unused output coordinate. -/
def constantCoordinateTest (P : AlphaTerm) : AlphaTerm := lam 90 (lam 91 (app P (var 90)))

theorem constantCoordinateTest_closed {P : AlphaTerm} (hP : P.Closed) :
    (constantCoordinateTest P).Closed := by
  unfold constantCoordinateTest Closed
  simp only [fv_lam,fv_app,fv_var]; rw [hP]; decide

theorem constantCoordinateTest_runs {P : AlphaTerm} (hP : P.Closed) (p : ℕ → ℕ) (n k v : ℕ)
    (hv : OracleRuns p P k v) : Relation.ReflTransGen (OracleStep p)
      (app (app (app (constantCoordinateTest P) (var 0)) (numeral n)) (numeral k)) (numeral v) := by
  have h₁ : Beta (app (constantCoordinateTest P) (var 0)) (lam 91 (app P (var 0))) := by
    convert Beta.contract 90 (lam 91 (app P (var 90))) (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 91 90 (by decide) (by simp [fv_var])]
    simp [subst_app,subst_var,subst_closed _ _ _ hP]
  have h₂ : Beta (app (lam 91 (app P (var 0))) (numeral n)) (app P (var 0)) := by
    simpa [subst_app,subst_var,subst_closed _ _ _ hP] using Beta.contract 91 (app P (var 0)) (numeral n)
  exact (beta_steps_oracle (Relation.ReflTransGen.tail
    (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂))).trans hv

end NamedLambda.AlphaTerm

def finiteSubcoverProgram (M N : AlphaTerm) : AlphaTerm :=
  mapOutputProgram (numericalProjectionTerm true)
    (searchProgram (constantCoordinateTest
      (mapOutputProgram reverseZeroTerm (subcoverStageProgram M N))))

theorem finiteSubcoverProgram_closed {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : (finiteSubcoverProgram A.program E.program).Closed :=
  mapOutputProgram_closed (projection_computes true).1
    (searchProgram_closed (constantCoordinateTest_closed
      ((subcoverStageProgram_computes A E).map reverseZero_computes).1))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Using the numerical bit negation $Z$ from the finite-net proof, put
    $$S:=\lambdaab{o}{\lambdaab{a}{\LambdaNumericProjection{1}
     \bigl(\LambdaSearch(\lambdaab{k}{Z(Dok)})\bigr)}}.$$
    The numerical argument $a$ is unused and may be set to $\ChurchNumeral{0}$. The sequential-search theorem from
    §{sec:lambda-input-search} returns the least successful pair; the final projection extracts its prefix length $m$.
    All constants are closed and both the enumeration argument and the dummy argument are bound, so $S$ is closed.
    The reductions above prove that $So\ChurchNumeral{0}$ returns $\ChurchNumeral{m}$ and that the first $m$ stages
    cover $K$. Uniqueness of numeral outputs excludes a different returned value. Discarding the empty stages leaves
    a finite subcover from the original enumeration.
    \end{proof}
-/
theorem finiteSubcoverProgram_runs [CompactSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) {p : ℕ → ℕ} (hp : IsEnumeratedCover q p) (a : ℕ) :
    ∃ m, OracleRuns p (finiteSubcoverProgram A.program E.program) a m ∧
      ∀ x, ∃ i < m, x ∈ enumeratedRationalBall q (p i) := by
  classical
  have hex := subcoverStageBit_exists A.toRationalMetricApproximation E.centers hp
  let j := Nat.find hex
  have hj : subcoverStageBit A.toRationalMetricApproximation E.centers p j ≠ 0 := Nat.find_spec hex
  have htest := (subcoverStageProgram_computes A E).map reverseZero_computes
  have ht (k : ℕ) := constantCoordinateTest_runs htest.1 p a k _ (htest.2 p k)
  have hr := searchProgram_hit (constantCoordinateTest_closed htest.1) a j
    (by simpa [hj] using ht j) (fun k hk => ⟨0,by
      have hz : subcoverStageBit A.toRationalMetricApproximation E.centers p k = 0 :=
        not_ne_iff.mp (Nat.find_min hex hk)
      simpa [hz] using ht k⟩)
  refine ⟨j.unpair.1,?_,subcoverStageBit_sound A.toRationalMetricApproximation E.covers p hj⟩
  exact mapOutputProgram_runs (projection_computes true).1
    (searchProgram_closed (constantCoordinateTest_closed htest.1)) hr ((projection_computes true).2 j)

theorem finiteSubcoverProgram_output [CompactSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) {p : ℕ → ℕ} (hp : IsEnumeratedCover q p) {a m : ℕ}
    (hm : OracleRuns p (finiteSubcoverProgram A.program E.program) a m) :
    ∀ x, ∃ i < m, x ∈ enumeratedRationalBall q (p i) := by
  obtain ⟨r,hr,hcover⟩ := finiteSubcoverProgram_runs A E hp a
  have he := oracle_numeral_output_unique hm hr
  simpa only [he] using hcover

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computing a finite subcover
-/
theorem finiteSubcover_selection [CompactSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) : ∃ P : AlphaTerm, P.Closed ∧
      ∀ p, IsEnumeratedCover q p → ∃ m, OracleRuns p P 0 m ∧
        ∀ x, ∃ i < m, x ∈ enumeratedRationalBall q (p i) :=
  ⟨finiteSubcoverProgram A.program E.program,finiteSubcoverProgram_closed A E,
    fun _ hp => finiteSubcoverProgram_runs A E hp 0⟩

end PolishSpaceBook
