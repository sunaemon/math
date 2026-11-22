module

public import PolishSpaceBook.LambdaImagePresentation
public import PolishSpaceBook.LambdaImageCovers
public import PolishSpaceBook.LambdaCompactNets
public import PolishSpaceBook.LambdaRationalOrder

@[expose] public section

/-! # Computable finite nets in the image presentation

Replace each image center by an ambient basic point and shrink its radius by
the approximation error. Search over the precision and a finite output
certificate for the ambient-cover semidecider, then use finite-cover/net equivalence.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

def recenteredBallCode (t : ℕ × ℕ → ℕ) (b n j : ℕ) : ℕ :=
  Nat.pair (t (coverBallCenter b j,n))
    ((coverBallRadius b j).add (RationalCode.dyadic n).neg).natCode

def recenteredCoverCode (t : ℕ × ℕ → ℕ) (b n : ℕ) : ℕ :=
  NatListCode.encode ((List.range (NatListCode.decode b).length).map (recenteredBallCode t b n))

/-- Input is `pair (pair b n) j`, as required by finite tabulation. -/
def recenteredBallProgram (T : AlphaTerm) : AlphaTerm :=
  let b := firstOutput (numericalProjectionTerm true)
  let n := secondOutput (numericalProjectionTerm true)
  let ball := numericalCompose listGetTerm (pairNumerical b (numericalProjectionTerm false))
  let center := numericalCompose T (pairNumerical (firstOutput ball) n)
  let radius := numericalCompose rationalAddTerm (pairNumerical (secondOutput ball)
    (numericalCompose rationalNegTerm (numericalCompose rationalDyadicTerm n)))
  pairNumerical center radius

theorem recenteredBallProgram_computes {T : AlphaTerm} {t : ℕ × ℕ → ℕ}
    (ht : NumericalComputes T (fun z => t z.unpair)) :
    NumericalComputes (recenteredBallProgram T)
      (fun z => recenteredBallCode t z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2) := by
  have hb := (projection_computes true).first
  have hn := (projection_computes true).second
  have hball := listGet_computes.comp (hb.pair (projection_computes false))
  have hc := ht.comp (hball.first.pair hn)
  have hr := rationalAdd_computes.comp (hball.second.pair
    (rationalNeg_computes.comp (rationalDyadic_computes.comp hn)))
  have h := hc.pair hr
  refine ⟨h.1,fun z => ?_⟩
  simpa [recenteredBallProgram,recenteredBallCode,coverBallCenter,coverBallRadius,
    RationalCode.ofNat_natCode] using h.2 z

def recenteredCoverProgram (T : AlphaTerm) : AlphaTerm :=
  numericalCompose (listTabulateTerm (recenteredBallProgram T))
    (pairNumerical numericalIdentity (numericalCompose listLengthTerm (numericalProjectionTerm true)))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    The conversion from the code $b$ of $C$ and the precision $n$ to the code $c(b,n)$ of $C_n$ is a total
    numerical computation. Here is an explicit term. Write $\pi_a:=\LambdaNumericProjection{a}$.
    A rational code $\NatPair{\NatPair{u}{v}}{w}$ denotes $(u-v)/(w+1)$, so negation is computed by
    $$J:=\lambdaab{z}{\LambdaNumericPair\,
     (\LambdaNumericPair\,(\pi_2(\pi_1z))\,(\pi_1(\pi_1z)))\,(\pi_2z)}.$$
    Let $T$ compute $t(i,n)$ on paired input. For an entry input $z=\NatPair{\NatPair{b}{n}}{j}$, define
    $$\begin{aligned}
    B&:=\lambdaab{z}{\LambdaListGet(\LambdaNumericPair\,(\pi_1(\pi_1z))\,(\pi_2z))},\\
    L&:=\lambdaab{z}{\pi_2(\pi_1z)},\\
    H&:=\lambdaab{z}{T(\LambdaNumericPair\,(\pi_1(Bz))\,(Lz))},\\
    R&:=\lambdaab{z}{\LambdaRationalAdd(\LambdaNumericPair\,(\pi_2(Bz))\,(J(\LambdaDyadic(Lz))))},\\
    G&:=\lambdaab{z}{\LambdaNumericPair\,(Hz)\,(Rz)},\\
    C^*&:=\lambdaab{z}{\LambdaListTabulate{G}
     (\LambdaNumericPair\,z\,(\LambdaListLength(\pi_1z)))}.
    \end{aligned}$$
    The term $B$ reads the old ball code, $L$ reads the precision, and $H,R$ compute the new center and radius.
    Swapping numerator components computes rational negation exactly; rational addition then computes
    $R_j-\varepsilon_n$. Finite tabulation gives $c(b,n)$, preserving the length and order of the list.
    These beta computations also handle the empty list and balls that become empty after shrinking.
-/
theorem recenteredCoverProgram_computes {T : AlphaTerm} {t : ℕ × ℕ → ℕ}
    (ht : NumericalComputes T (fun z => t z.unpair)) :
    NumericalComputes (recenteredCoverProgram T) (fun z => recenteredCoverCode t z.unpair.1 z.unpair.2) := by
  have h := (listTabulate_computes (recenteredBallProgram_computes ht)).comp
    (numericalIdentity_computes.pair (listLength_computes.comp (projection_computes true)))
  refine ⟨h.1,fun z => ?_⟩
  simpa [recenteredCoverProgram,recenteredCoverCode] using h.2 z

@[simp] theorem recenteredCoverCode_length (t : ℕ × ℕ → ℕ) (b n : ℕ) :
    (NatListCode.decode (recenteredCoverCode t b n)).length = (NatListCode.decode b).length := by
  simp [recenteredCoverCode]

theorem recenteredCoverCode_entry (t : ℕ × ℕ → ℕ) (b n j : ℕ)
    (hj : j < (NatListCode.decode b).length) :
    (NatListCode.decode (recenteredCoverCode t b n)).getD j 0 = recenteredBallCode t b n j := by
  simp [recenteredCoverCode,List.getD,hj]

theorem recenteredCoverCode_center (t : ℕ × ℕ → ℕ) (b n j : ℕ)
    (hj : j < (NatListCode.decode b).length) :
    coverBallCenter (recenteredCoverCode t b n) j = t (coverBallCenter b j,n) := by
  simp only [coverBallCenter,recenteredCoverCode_entry t b n j hj,recenteredBallCode,Nat.unpair_pair]

theorem recenteredCoverCode_radius (t : ℕ × ℕ → ℕ) (b n j : ℕ)
    (hj : j < (NatListCode.decode b).length) :
    ((coverBallRadius (recenteredCoverCode t b n) j).value : ℝ) =
      (coverBallRadius b j).value - (1/2:ℝ)^n := by
  simp only [coverBallRadius,recenteredCoverCode_entry t b n j hj,recenteredBallCode,Nat.unpair_pair,
    RationalCode.ofNat_natCode,RationalCode.value_add,RationalCode.value_neg]
  push_cast
  simp [sub_eq_add_neg]

variable {qX : ℕ → X} {qY : ℕ → Y} {f : X → Y}

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the preceding presentation and its approximation function $t$, so that
    $d(r_i,s_{t(i,n)})\le\varepsilon_n:=2^{-n}$ for the ambient basic points $s_j$.
    Given a finite list $C=((i_j,R_j))_{j<\ell}$ of rational balls centered at the image points, form the ambient list
    $$C_n:=((t(i_j,n),R_j-\varepsilon_n))_{j<\ell}.$$
    Nonpositive radii denote empty balls. If $C_n$ covers $f[K]$, then $C$ covers it: for a point in a ball of $C_n$,
    $$d(y,r_{i_j})\le d(y,s_{t(i_j,n)})+\varepsilon_n<R_j.$$
    Conversely, if $C$ covers $f[K]$, the \termuse{uniform ball-cover margin} applied to the compact metric space
    $f[K]$ gives some $n$ such that each
    $y\in f[K]$ satisfies $d(y,r_{i_j})+4\varepsilon_n<R_j$ for some $j<\ell$. Then
    $$d(y,s_{t(i_j,n)})\le d(y,r_{i_j})+\varepsilon_n<R_j-\varepsilon_n.$$
    Thus $C_n$ covers $f[K]$. We have proved that $C$ is a cover exactly when some $C_n$ is a cover.
-/
omit [MetricSpace X] in
theorem recenteredCover_sound (T : DensePointApproximation (fun i => f (qX i)) qY) (b n : ℕ)
    (h : imageBallListCovers qY f (recenteredCoverCode T.index b n)) :
    rationalBallListCovers (imageDenseSequence qX f) b := by
  rintro ⟨y,x,rfl⟩
  obtain ⟨j,hj,hx⟩ := h x
  rw [recenteredCoverCode_length] at hj
  rw [recenteredCoverCode_center _ _ _ _ hj,recenteredCoverCode_radius _ _ _ _ hj] at hx
  refine ⟨j,hj,?_⟩
  change dist (f x) (f (qX (coverBallCenter b j))) < _
  have he := T.error (coverBallCenter b j) n
  have hd := dist_triangle (f x) (qY (T.index (coverBallCenter b j,n))) (f (qX (coverBallCenter b j)))
  rw [dist_comm (qY _)] at hd
  linarith

omit [MetricSpace X] in
theorem recenteredCover_complete [CompactSpace (Set.range f)]
    (T : DensePointApproximation (fun i => f (qX i)) qY) {b : ℕ}
    (h : rationalBallListCovers (imageDenseSequence qX f) b) :
    ∃ n, imageBallListCovers qY f (recenteredCoverCode T.index b n) := by
  obtain ⟨n,hn⟩ := rationalBallListCovers_uniform_margin (imageDenseSequence qX f) h
  refine ⟨n,fun x => ?_⟩
  obtain ⟨j,hj,hx⟩ := hn ⟨f x,x,rfl⟩
  refine ⟨j,by simpa using hj,?_⟩
  rw [recenteredCoverCode_center _ _ _ _ hj,recenteredCoverCode_radius _ _ _ _ hj]
  change dist (f x) (f (qX (coverBallCenter b j))) + 4*(1/2:ℝ)^n < _ at hx
  have he := T.error (coverBallCenter b j) n
  have hd := dist_triangle (f x) (f (qX (coverBallCenter b j))) (qY (T.index (coverBallCenter b j,n)))
  have hp : 0 < (1/2:ℝ)^n := by positivity
  linarith

def recenteredCoverCandidate (t : ℕ × ℕ → ℕ) (e z : ℕ) : ℕ :=
  if Term.outputCandidate e (recenteredCoverCode t z.unpair.1 z.unpair.2.unpair.1)
    z.unpair.2.unpair.2 then 1 else 0

def recenteredCoverCandidateProgram (T : AlphaTerm) (e : ℕ) : AlphaTerm :=
  numericalApply3 outputCandidateTerm (numericalConstant e)
    (numericalCompose (recenteredCoverProgram T) (pairNumerical (numericalProjectionTerm true)
      (firstOutput (numericalProjectionTerm false))))
    (secondOutput (numericalProjectionTerm false))

theorem recenteredCoverCandidateProgram_computes {T : AlphaTerm} {t : ℕ × ℕ → ℕ}
    (ht : NumericalComputes T (fun z => t z.unpair)) (e : ℕ) :
    NumericalComputes (recenteredCoverCandidateProgram T e) (recenteredCoverCandidate t e) := by
  have hb := (recenteredCoverProgram_computes ht).comp
    ((projection_computes true).pair (projection_computes false).first)
  have hc := (projection_computes false).second
  have h := (numericalConstant_computes e).apply3 hb hc outputCandidateTerm_closed
    (fun a b c => if Term.outputCandidate a b c then 1 else 0) outputCandidateTerm_apply
  refine ⟨h.1,fun z => ?_⟩
  simpa [recenteredCoverCandidateProgram,recenteredCoverCandidate] using h.2 z

def recenteredCoverSemidecider (T : AlphaTerm) (e : ℕ) : AlphaTerm :=
  numericalSearch (recenteredCoverCandidateProgram T e)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Let $P_e$ be the ambient finite-cover semidecider constructed above. Do not wait for it on one fixed precision:
    a noncover need not terminate. Instead search over $k=\NatPair{n}{a}$, where $a$ is a finite output
    certificate for $P_e\ChurchNumeral{c(b,n)}$. Explicitly, use
    $$\begin{aligned}
    W&:=\lambdaab{z}{C^*(\LambdaNumericPair\,(\pi_1z)\,(\pi_1(\pi_2z)))},\\
    D_e&:=\lambdaab{z}{\LambdaOutputCandidate\,\ChurchNumeral{e}\,(Wz)\,(\pi_2(\pi_2z))},\\
    G_{e,b}&:=\lambdaab{k}{Z(D_e(\LambdaNumericPair\,b\,k))},\\
    S_e&:=\lambdaab{b}{\LambdaResultSearch\,G_{e,b}\,I}.
    \end{aligned}$$
    Here $Z$ negates the test bit and $I$ is the identity term. Each certificate test terminates. A successful test
    certifies that $C_n$ covers the image, so $C$ covers it. Conversely, a covering $C$ supplies a suitable $n$;
    the ambient semidecider then has a numeral output, which has a finite certificate. The exact search theorem
    therefore makes $S_e$ a semidecider whose domain is precisely the image-centered finite covers.
-/
omit [MetricSpace X] in
theorem recenteredCoverSemidecider_spec [CompactSpace (Set.range f)]
    (T : DensePointApproximation (fun i => f (qX i)) qY) {e : ℕ}
    (he : ∀ b, (∃ m, Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral b)) (numeral m)) ↔
      imageBallListCovers qY f b) (b : ℕ) :
    (∃ m, Relation.ReflTransGen Beta (app (recenteredCoverSemidecider T.program e) (numeral b)) (numeral m)) ↔
      rationalBallListCovers (imageDenseSequence qX f) b := by
  rw [recenteredCoverSemidecider,numericalSearch_domain (recenteredCoverCandidateProgram_computes T.computes e)]
  constructor
  · rintro ⟨k,hk⟩
    have hcert : Term.outputCandidate e (recenteredCoverCode T.index b k.unpair.1) k.unpair.2 = true := by
      simpa [recenteredCoverCandidate] using hk
    have hout := (outputTest_exists_iff _ _ _).mp ⟨_,hcert⟩
    exact recenteredCover_sound T b k.unpair.1 ((he _).mp ⟨_,hout⟩)
  · intro hb
    obtain ⟨n,hn⟩ := recenteredCover_complete T hb
    obtain ⟨m,hm⟩ := (he _).mpr hn
    obtain ⟨s,hs⟩ := (outputTest_exists_iff _ _ _).mpr hm
    refine ⟨Nat.pair n (Nat.pair m s),?_⟩
    simp [recenteredCoverCandidate,Term.outputCandidate,hs]

/-- The construction uses image centers, not ambient centers outside the image. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: theorem
  title: Computable compactness of images
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Finally apply the \termuseas{computable compactness equivalence}{finite-cover/net equivalence} to the complete
    image presentation and this semidecider. Its construction searches finite prefixes of the image sequence together
    with output certificates, and returns a list $(i)_{i<m(n)}$ such that
    $$f[K]\IncludedIn\bigcup_{i<m(n)}\Ball{r_i}{2^{-n}}.$$
    The prefix-existence argument uses compactness and density; the certificate search supplies the computable choice.
    Every returned center lies in $f[K]$, and the same closed program works for every $n$.
    \end{proof}
-/
theorem computable_image_has_finiteNets [CompleteSpace X] [CompleteSpace Y] [CompactSpace X]
    (A : LambdaMetricApproximation qX) (B : LambdaMetricApproximation qY) (N : LambdaFiniteNets qX)
    (hqX : DenseRange qX) (hqY : DenseRange qY)
    (hf : HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f) :
    Nonempty (LambdaFiniteNets (imageDenseSequence qX f)) := by
  obtain ⟨hc,_,hd,⟨M⟩⟩ := computable_image_presentation hqX hqY B hf
  let := hc
  obtain ⟨T⟩ := imagePointApproximation_of_realizer hqX hqY hf
  obtain ⟨P,hP,hcov⟩ := computable_image_has_coverSemidecider A B N hqX hqY f hf
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
  have hindex : ∀ b, (∃ m, Relation.ReflTransGen Beta
      (app (Term.closedProgram e) (numeral b)) (numeral m)) ↔ imageBallListCovers qY f b := by
    simpa only [he] using hcov
  have hs := numericalSearch_closed (recenteredCoverCandidateProgram_computes T.computes e).1
  obtain ⟨d,hd'⟩ := Term.closedProgram_surjective (recenteredCoverSemidecider T.program e) hs
  apply (finiteNets_iff_coverSemidecision M hd).mpr
  refine ⟨d,fun b => ?_⟩
  rw [hd']
  exact recenteredCoverSemidecider_spec T hindex b

end PolishSpaceBook
