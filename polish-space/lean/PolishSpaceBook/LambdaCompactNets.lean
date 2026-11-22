module

public import PolishSpaceBook.LambdaCompactCovers
public import PolishSpaceBook.LambdaListTabulation
public import PolishSpaceBook.LambdaNumericalResultSearch

@[expose] public section

/-! # Computable finite nets from semidecision of finite covers

Search over pairs of a prefix length and a finite beta-output certificate.
Every test terminates, even when the candidate cover's semidecision diverges.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set
universe u
variable {X : Type u} [MetricSpace X]

def dyadicPrefixBallCode (n m : ℕ) : ℕ :=
  NatListCode.encode ((List.range m).map (fun i => Nat.pair i (RationalCode.dyadic n).natCode))

theorem dyadicPrefixBallCode_covers (q : ℕ → X) (n m : ℕ) :
    rationalBallListCovers q (dyadicPrefixBallCode n m) ↔
      ∀ x, ∃ i < m, dist x (q i) < (1/2:ℝ)^n := by
  simp only [rationalBallListCovers,dyadicPrefixBallCode,NatListCode.decode_encode,
    List.length_map,List.length_range,coverBallCenter,coverBallRadius]
  have he (i : ℕ) (hi : i < m) :
      ((List.range m).map (fun i => Nat.pair i (RationalCode.dyadic n).natCode)).getD i 0 =
        Nat.pair i (RationalCode.dyadic n).natCode := by
    simp [List.getD,hi]
  constructor <;> intro h x <;> obtain ⟨i,hi,hx⟩ := h x <;> refine ⟨i,hi,?_⟩
  · simpa only [he i hi,Nat.unpair_pair,RationalCode.ofNat_natCode,
      RationalCode.value_dyadic,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hx
  · simpa only [he i hi,Nat.unpair_pair,RationalCode.ofNat_natCode,
      RationalCode.value_dyadic,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hx

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The preceding lemma proves the forward direction. For the converse, let $P_e$ semidecide finite covers:
    it has a numeral output on a ball-list code exactly when that list covers $K$. Fix $n$. Density gives
    $$K=\bigcup_{i\in\NN}\Ball{q_i}{2^{-n}}.$$
    Compactness supplies a finite subcover. Choose $m$ larger than every index in that subcover; then the first $m$
    balls already cover $K$. We therefore need only search the prefix lists
    $$B_{n,m}:=((i,2^{-n}))_{i<m}.$$
    No effective choice of the finite subcover or of this bound is used here: this argument only proves that a
    successful prefix exists.
-/
theorem exists_dyadicPrefixBallCode_cover [CompactSpace X] (q : ℕ → X)
    (hq : DenseRange q) (n : ℕ) : ∃ m, rationalBallListCovers q (dyadicPrefixBallCode n m) := by
  have hc : (univ : Set X) ⊆ ⋃ i, Metric.ball (q i) ((1/2:ℝ)^n) := by
    intro x _
    obtain ⟨i,hi⟩ := hq.exists_dist_lt x (by positivity : 0 < (1/2:ℝ)^n)
    exact mem_iUnion.mpr ⟨i,hi⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => Metric.ball (q i) ((1/2:ℝ)^n)) (fun _ => Metric.isOpen_ball) hc
  refine ⟨s.sup id + 1,(dyadicPrefixBallCode_covers q n _).mpr ?_⟩
  intro x
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
  exact ⟨i,Nat.lt_succ_of_le (Finset.le_sup (f := id) his),hxi⟩

def dyadicPrefixBallProgram : AlphaTerm :=
  listTabulateTerm (pairNumerical (numericalProjectionTerm false)
    (numericalCompose rationalDyadicTerm (numericalProjectionTerm true)))

theorem dyadicPrefixBallProgram_computes : NumericalComputes dyadicPrefixBallProgram
    (fun z => dyadicPrefixBallCode z.unpair.1 z.unpair.2) := by
  have h := listTabulate_computes ((projection_computes false).pair
    (rationalDyadic_computes.comp (projection_computes true)))
  simpa only [dyadicPrefixBallProgram,dyadicPrefixBallCode,Nat.unpair_pair,
    Bool.false_eq_true,ite_false,ite_true] using h

def prefixCoverCertificateBit (e z : ℕ) : ℕ :=
  if Term.outputCandidate e (dyadicPrefixBallCode z.unpair.1 z.unpair.2.unpair.1)
    z.unpair.2.unpair.2 then 1 else 0

def prefixCoverCertificateProgram (e : ℕ) : AlphaTerm :=
  numericalApply3 outputCandidateTerm (numericalConstant e)
    (numericalCompose dyadicPrefixBallProgram (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))

theorem prefixCoverCertificateProgram_computes (e : ℕ) :
    NumericalComputes (prefixCoverCertificateProgram e) (prefixCoverCertificateBit e) := by
  have input := dyadicPrefixBallProgram_computes.comp ((projection_computes true).pair
    ((projection_computes true).comp (projection_computes false)))
  have cert := (projection_computes false).comp (projection_computes false)
  have h := (numericalConstant_computes e).apply3 input cert outputCandidateTerm_closed
    (fun a b c => if Term.outputCandidate a b c then 1 else 0) outputCandidateTerm_apply
  refine ⟨h.1,fun z => ?_⟩
  simpa only [prefixCoverCertificateProgram,prefixCoverCertificateBit,Nat.unpair_pair,
    Bool.false_eq_true,ite_false,ite_true] using h.2 z

def IsCoverSemidecisionIndex (q : ℕ → X) (e : ℕ) : Prop :=
  ∀ b, (∃ m, Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral b)) (numeral m)) ↔
    rationalBallListCovers q b

theorem prefixCoverCertificateBit_sound {q : ℕ → X} {e : ℕ}
    (he : IsCoverSemidecisionIndex q e) (n k : ℕ)
    (hk : prefixCoverCertificateBit e (Nat.pair n k) ≠ 0) :
    rationalBallListCovers q (dyadicPrefixBallCode n k.unpair.1) := by
  have ht : Term.outputCandidate e (dyadicPrefixBallCode n k.unpair.1) k.unpair.2 = true := by
    simpa [prefixCoverCertificateBit] using hk
  exact (he _).mp ⟨k.unpair.2.unpair.1,(outputTest_exists_iff _ _ _).mp ⟨_,ht⟩⟩

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Let $b(n,m)$ be the numerical code of $B_{n,m}$. It is computable by finite tabulation. Explicitly, put
    $$\begin{aligned}
    H&:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,
      (\LambdaDyadic(\LambdaNumericProjection{1}z))},\\
    B&:=\LambdaListTabulate{H}.
    \end{aligned}$$
    Then $B$ sends $\ChurchNumeral{\NatPair{n}{m}}$ to $\ChurchNumeral{b(n,m)}$.
    To avoid waiting forever for a noncover, search over pairs $k=\NatPair{m}{c}$, where $c$ is an output-candidate
    code for $P_e$ on input $b(n,m)$. The finite tester in §{sec:lambda-program-input-codes} gives the closed terms
    $$\begin{aligned}
    V&:=\lambdaab{z}{B(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,
       (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z)))},\\
    Q&:=\lambdaab{z}{\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z)},\\
    C_e&:=\lambdaab{z}{\LambdaOutputCandidate\,\ChurchNumeral{e}\,(Vz)\,(Qz)}.
    \end{aligned}$$
    On input $\NatPair{n}{\NatPair{m}{c}}$, it returns $1$ exactly when $c$ certifies a numeral output of
    $P_e\ChurchNumeral{b(n,m)}$, and returns $0$ otherwise. Every test terminates. Soundness of the certificate tester
    shows that every successful test gives a cover. Conversely, a covering prefix makes $P_e$ return a numeral,
    and completeness of the tester supplies a successful certificate. Thus, for each $n$, some paired candidate succeeds.
-/
theorem prefixCoverCertificateBit_exists [CompactSpace X] {q : ℕ → X} (hq : DenseRange q)
    {e : ℕ} (he : IsCoverSemidecisionIndex q e) (n : ℕ) :
    ∃ k, prefixCoverCertificateBit e (Nat.pair n k) ≠ 0 := by
  obtain ⟨m,hm⟩ := exists_dyadicPrefixBallCode_cover q hq n
  obtain ⟨v,hv⟩ := (he _).mpr hm
  obtain ⟨s,hs⟩ := (outputTest_exists_iff _ _ _).mpr hv
  refine ⟨Nat.pair m (Nat.pair v s),?_⟩
  simp only [prefixCoverCertificateBit,Nat.unpair_pair,Term.outputCandidate,hs,ite_true]
  decide

def prefixNetListProgram : AlphaTerm :=
  numericalCompose (listTabulateTerm (numericalProjectionTerm false))
    (pairNumerical (numericalConstant 0) (numericalProjectionTerm true))

theorem prefixNetListProgram_computes : NumericalComputes prefixNetListProgram
    (fun k => NatListCode.encode (List.range k.unpair.1)) := by
  have h := (listTabulate_computes (projection_computes false)).comp
    ((numericalConstant_computes 0).pair (projection_computes true))
  refine ⟨h.1,fun z => ?_⟩
  simpa [prefixNetListProgram] using h.2 z

def coverNetProgram (e : ℕ) : AlphaTerm :=
  numericalCompose prefixNetListProgram (numericalSearch (prefixCoverCertificateProgram e))

noncomputable def coverNetSequence (e : ℕ)
    (h : ∀ n, ∃ k, prefixCoverCertificateBit e (Nat.pair n k) ≠ 0) (n : ℕ) : List ℕ :=
  List.range (firstNumericalHit (prefixCoverCertificateBit e) h n).unpair.1

theorem coverNetProgram_computes (e : ℕ)
    (h : ∀ n, ∃ k, prefixCoverCertificateBit e (Nat.pair n k) ≠ 0) :
    NumericalComputes (coverNetProgram e) (fun n => NatListCode.encode (coverNetSequence e h n)) :=
  prefixNetListProgram_computes.comp
    (numericalSearch_computes (prefixCoverCertificateProgram_computes e) h)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Using $Z$ and $I$ from the preceding proof, define
    $$\begin{aligned}
    G_{e,n}&:=\lambdaab{k}{Z(C_e(\LambdaNumericPair\,n\,k))},\\
    J_e&:=\lambdaab{n}{\LambdaResultSearch\,G_{e,n}\,I},\\
    R&:=\lambdaab{k}{\LambdaListTabulate{\LambdaNumericProjection{2}}
       (\LambdaNumericPair\,\ChurchNumeral{0}\,(\LambdaNumericProjection{1}k))},\\
    F_e&:=\lambdaab{n}{R(J_en)}.
    \end{aligned}$$
    Search returns the least successful paired candidate, and $R$ tabulates the indices $i<m$ from its first component.
    Consequently, $F_e\ChurchNumeral{n}$ returns the code of a finite list whose $2^{-n}$-balls cover $K$.
    Expanding the parameterized abbreviation $G_{e,n}$ in $F_e$ binds every variable; $e$ is inserted as a numeral.
    Thus $F_e$ is a closed term built by fixed compositions. Finite tabulation and the exact search theorem prove
    the stated beta reductions. The syntax construction
    retains the given semidecider index and requires no extra oracle. This proves the converse and the equivalence.
    \end{proof}
-/
noncomputable def finiteNetsOfCoverSemidecision [CompactSpace X] {q : ℕ → X} (hq : DenseRange q)
    (e : ℕ) (he : IsCoverSemidecisionIndex q e) : LambdaFiniteNets q where
  centers := coverNetSequence e (prefixCoverCertificateBit_exists hq he)
  program := coverNetProgram e
  computes := coverNetProgram_computes e (prefixCoverCertificateBit_exists hq he)
  covers := by
    intro n x
    have hcover := prefixCoverCertificateBit_sound he n _
      (Nat.find_spec (prefixCoverCertificateBit_exists hq he n))
    obtain ⟨i,hi,hxi⟩ := (dyadicPrefixBallCode_covers q n _).mp hcover x
    refine ⟨i,by simpa [coverNetSequence,firstNumericalHit] using hi,?_⟩
    simpa [coverNetSequence,firstNumericalHit,List.getD,List.getElem?_eq_getElem,hi] using hxi

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: theorem
  title: Finite nets and finite-cover semidecision
-/
theorem finiteNets_iff_coverSemidecision [CompactSpace X] {q : ℕ → X}
    (A : LambdaMetricApproximation q) (hq : DenseRange q) :
    Nonempty (LambdaFiniteNets q) ↔ ∃ e, IsCoverSemidecisionIndex q e := by
  constructor
  · rintro ⟨E⟩
    obtain ⟨e,he⟩ := Term.closedProgram_surjective _ (netCoverSemidecider_closed A E)
    exact ⟨e,fun b => by rw [he]; exact netCoverSemidecider_spec A E b⟩
  · rintro ⟨e,he⟩
    exact ⟨finiteNetsOfCoverSemidecision hq e he⟩

end PolishSpaceBook
