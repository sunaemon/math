module

public import PolishSpaceBook.LambdaImageNets
public import PolishSpaceBook.LambdaRealMetric
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! # Supremum names computed from finite nets

Start the rational maximum at the approximation of a fixed image point, so
negative-valued functions are handled without a spurious zero lower bound.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- A finite maximum with a supplied seed code. -/
def maximumCodes (seed : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  primitiveRec seed (fun j acc => rationalMaxCode acc (a j)) n

theorem maximumCodes_le (seed : ℕ) (a : ℕ → ℕ) (n : ℕ) (M : ℝ)
    (hs : rationalPoint seed ≤ M) (ha : ∀ j < n, rationalPoint (a j) ≤ M) :
    rationalPoint (maximumCodes seed a n) ≤ M := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    change rationalPoint (rationalMaxCode (maximumCodes seed a n) (a n)) ≤ M
    rw [rationalPoint_max]
    exact max_le (ih (fun j hj => ha j (by omega))) (ha n (by omega))

theorem le_maximumCodes (seed : ℕ) (a : ℕ → ℕ) {n j : ℕ} (hj : j < n) :
    rationalPoint (a j) ≤ rationalPoint (maximumCodes seed a n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    change rationalPoint (a j) ≤ rationalPoint (rationalMaxCode (maximumCodes seed a n) (a n))
    rw [rationalPoint_max]
    by_cases h : j < n
    · exact (ih h).trans (le_max_left _ _)
    · have he : j = n := by omega
      rw [he]; exact le_max_right _ _

def netValueMaximum (E : ℕ → List ℕ) (t : ℕ × ℕ → ℕ) (k : ℕ) : ℕ :=
  maximumCodes (t (0,k)) (fun j => t ((E k).getD j 0,k)) (E k).length

def netMaximumSeedProgram (T : AlphaTerm) : AlphaTerm :=
  numericalCompose T (pairNumerical (numericalConstant 0) numericalIdentity)

def netMaximumStepProgram (N T : AlphaTerm) : AlphaTerm :=
  let k := numericalProjectionTerm true
  let j := firstOutput (numericalProjectionTerm false)
  let acc := secondOutput (numericalProjectionTerm false)
  let entry := numericalCompose listGetTerm (pairNumerical (numericalCompose N k) j)
  numericalCompose rationalMaxProgram (pairNumerical acc (numericalCompose T (pairNumerical entry k)))

def netMaximumProgram (N T : AlphaTerm) : AlphaTerm :=
  numericalCompose (numericalRecursion (netMaximumSeedProgram T) (netMaximumStepProgram N T))
    (pairNumerical numericalIdentity (numericalCompose listLengthTerm N))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Here is the closed name-generating term. Let $N$ compute the list code of $E_k$, let $T$ compute $t(i,k)$
    on paired input, and use the rational maximum term $V$ from the lemma. Define
    $$\begin{aligned}
    L&:=\lambdaab{k}{\lambdaab{j}{\LambdaListGet(\LambdaNumericPair\,(Nk)\,j)}},\\
    W&:=\lambdaab{k}{\lambdaab{j}{T(\LambdaNumericPair\,(Lkj)\,k)}},\\
    B&:=\lambdaab{k}{T(\LambdaNumericPair\,\ChurchNumeral{0}\,k)},\\
    H&:=\lambdaab{k}{\lambdaab{j}{\lambdaab{a}{V(\LambdaNumericPair\,a\,(Wkj))}}},\\
    C&:=\lambdaab{k}{\LambdaParamRec{B}{H}\,k\,(\LambdaListLength(Nk))},\\
    P&:=\lambdaab{n}{C(\LambdaSucc(\LambdaSucc n))}.
    \end{aligned}$$
    The term $B$ returns the seed code. At step $j$, $L$ reads the net index, $W$ approximates that image point,
    and $H$ takes the rational maximum with the accumulator. Induction on the finite recursion shows that $C$
    returns a code $c(k)$ for $b_k$. All component computations terminate. Thus $P$ computes
    $p(n):=c(n+2)$ by ordinary beta reduction. Expanding the auxiliary terms leaves a closed term, and the
    preceding error estimate proves that its output sequence is a valid name of $M$.
    \end{proof}
-/
theorem netMaximumProgram_computes {N T : AlphaTerm} {E : ℕ → List ℕ} {t : ℕ × ℕ → ℕ}
    (hN : NumericalComputes N (fun k => NatListCode.encode (E k)))
    (hT : NumericalComputes T (fun z => t z.unpair)) :
    NumericalComputes (netMaximumProgram N T) (netValueMaximum E t) := by
  have hb := hT.comp ((numericalConstant_computes 0).pair numericalIdentity_computes)
  have hk := projection_computes true
  have hj := (projection_computes false).first
  have hr := (projection_computes false).second
  have he := listGet_computes.comp ((hN.comp hk).pair hj)
  have hs := rationalMaxProgram_computes.comp (hr.pair (hT.comp (he.pair hk)))
  have h := (numericalRecursion_computes hb hs).comp
    (numericalIdentity_computes.pair (listLength_computes.comp hN))
  refine ⟨h.1,fun z => ?_⟩
  simpa [netMaximumProgram,netMaximumSeedProgram,netMaximumStepProgram,netValueMaximum,maximumCodes] using h.2 z

universe u
variable {X : Type u} {q : ℕ → X} {f : X → ℝ}

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $M:=\sup f[K]$. This is finite because $f[K]$ is nonempty and compact. Write $r_i=f(q_i)$ for its basic
    points. The image theorem supplies computable finite nets
    $$\begin{aligned}
    E_k&=(e_{k,j})_{j<\ell_k},\qquad \varepsilon_k:=2^{-k},\\
    f[K]&\IncludedIn\bigcup_{j<\ell_k}\Ball{r_{e_{k,j}}}{\varepsilon_k}.
    \end{aligned}$$
    Applying the realizer to constant names supplies a computable function $t$ with rational approximations
    $$a_{i,k}:=s_{t(i,k)},\qquad |a_{i,k}-r_i|\le\varepsilon_k.$$
    Compute the finite maximum by the recurrence
    $$\begin{aligned}
    v_{k,0}&:=a_{0,k},\\
    v_{k,j+1}&:=\max(v_{k,j},a_{e_{k,j},k})\quad(j<\ell_k),\\
    b_k&:=v_{k,\ell_k}.
    \end{aligned}$$
    The seed is the approximation of a fixed image point. In particular, the recurrence remains valid when the
    function takes only negative values.
-/

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Each value entering the maximum is at most $M+\varepsilon_k$, since its center lies in the image.
    Induction over the list therefore gives $b_k\le M+\varepsilon_k$. Conversely, for every $y\in f[K]$,
    choose a net index $e_{k,j}$ with $|y-r_{e_{k,j}}|<\varepsilon_k$. Then
    $$y<r_{e_{k,j}}+\varepsilon_k\le a_{e_{k,j},k}+2\varepsilon_k\le b_k+2\varepsilon_k.$$
    Taking the supremum yields
    $$M\le b_k+2\varepsilon_k,\qquad |b_k-M|\le 2\varepsilon_k.$$
    Consequently $u_n:=b_{n+2}$ satisfies $|u_n-M|\le 2^{-(n+1)}$.
    For $m\ge n$ this gives
    $$|u_n-u_m|\le 2^{-(n+1)}+2^{-(m+1)}\le 2^{-n},$$
    so these rationals form a fast Cauchy name converging to the required supremum.
-/
theorem netValueMaximum_error (N : LambdaFiniteNets (imageDenseSequence q f))
    (T : DensePointApproximation (fun i => f (q i)) rationalPoint)
    (hbdd : BddAbove (Set.range f)) (k : ℕ) :
    |rationalPoint (netValueMaximum N.centers T.index k) - sSup (Set.range f)| ≤ 2*(1/2:ℝ)^k := by
  let M := sSup (Set.range f)
  let v := rationalPoint (netValueMaximum N.centers T.index k)
  have hpoint (i : ℕ) : f (q i) ≤ M := le_csSup hbdd ⟨q i,rfl⟩
  have happrox (i : ℕ) : rationalPoint (T.index (i,k)) ≤ M + (1/2:ℝ)^k := by
    have he := (abs_le.mp (T.error i k)).1
    have hi := hpoint i
    linarith
  have hv : v ≤ M + (1/2:ℝ)^k :=
    maximumCodes_le (T.index (0,k)) (fun j => T.index ((N.centers k).getD j 0,k))
      (N.centers k).length _ (happrox 0) (fun j _ => happrox _)
  have hupper (y : ℝ) (hy : y ∈ Set.range f) : y ≤ v + 2*(1/2:ℝ)^k := by
    obtain ⟨x,rfl⟩ := hy
    obtain ⟨j,hj,hd⟩ := N.covers k ⟨f x,x,rfl⟩
    change |f x - f (q ((N.centers k).getD j 0))| < (1/2:ℝ)^k at hd
    have he := (abs_le.mp (T.error ((N.centers k).getD j 0) k)).2
    have hm : rationalPoint (T.index ((N.centers k).getD j 0,k)) ≤ v :=
      le_maximumCodes (T.index (0,k)) (fun j => T.index ((N.centers k).getD j 0,k)) hj
    have ht := (le_abs_self (f x - f (q ((N.centers k).getD j 0)))).trans_lt hd
    linarith
  have hm : M ≤ v + 2*(1/2:ℝ)^k := csSup_le ⟨f (q 0),q 0,rfl⟩ hupper
  have hp : 0 ≤ (1/2:ℝ)^k := by positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A two-level shift turns the maximum estimates into a fast Cauchy name. -/
theorem computable_supremum_from_nets (N : LambdaFiniteNets (imageDenseSequence q f))
    (T : DensePointApproximation (fun i => f (q i)) rationalPoint)
    (hbdd : BddAbove (Set.range f)) : IsComputablePoint realRepresentation (sSup (Set.range f)) := by
  let p : ℕ → ℕ := fun n => netValueMaximum N.centers T.index (n+2)
  have hp (n : ℕ) : dist (rationalPoint (p n)) (sSup (Set.range f)) ≤ (1/2:ℝ)^(n+1) := by
    calc
      _ ≤ 2*(1/2:ℝ)^(n+2) := netValueMaximum_error N T hbdd (n+2)
      _ = _ := by ring
  have hP := (netMaximumProgram_computes N.computes T.computes).comp
    (successor_computes.comp successor_computes)
  have hP' : NumericalComputes
      (numericalCompose (netMaximumProgram N.program T.program) (numericalCompose successorTerm successorTerm)) p := by
    simpa [p,Nat.succ_eq_add_one,Nat.add_assoc] using hP
  refine ⟨⟨p,isCauchyName_of_halfError_le hp⟩,⟨_,hP'⟩,?_⟩
  exact cauchyRepresentation_eq_of_halfError_le p _ hp

/-- The source's finite nets suffice; no modulus of continuity is additional input. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computable suprema
-/
theorem computable_supremum [MetricSpace X] [CompleteSpace X] [CompactSpace X]
    (A : LambdaMetricApproximation q) (N : LambdaFiniteNets q) (hq : DenseRange q)
    (hf : HasComputableRealizer (cauchyRepresentationObject q hq) realRepresentation f) :
    IsComputablePoint realRepresentation (sSup (Set.range f)) := by
  obtain ⟨E⟩ := computable_image_has_finiteNets A realMetricApproximation N hq rationalPoint_dense hf
  obtain ⟨T⟩ := imagePointApproximation_of_realizer hq rationalPoint_dense hf
  have hc := hf.continuous (cauchyRepresentationObject_isAdmissible q hq)
    (continuous_cauchyRepresentation rationalPoint)
  exact computable_supremum_from_nets E T (isCompact_range hc).bddAbove

end PolishSpaceBook
