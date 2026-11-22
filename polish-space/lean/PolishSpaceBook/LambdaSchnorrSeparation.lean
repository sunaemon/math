module

public import PolishSpaceBook.LambdaPositiveClosedBound

@[expose] public section

/-! # A Schnorr-random point which is not Martin-Löf random
The finite steps use the preceding lambda constructions. The enumeration of
all valid Schnorr tests is set-theoretic; no decision procedure for test indices
or computable choice of the infinite sequence is asserted.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem computablyMeasured_empty : ComputablyMeasuredOpen (∅ : Set (ℕ → Bool)) := by
  simpa only [finiteOpen_nil] using computablyMeasured_finiteOpen [] (by simp)

theorem SchnorrTest.computablyMeasured_row {U : ℕ → Set (ℕ → Bool)} (hU : SchnorrTest U) (n : ℕ) :
    ComputablyMeasuredOpen (U n) := by
  obtain ⟨P,p,hp,hv,hn⟩ := hU.1.1
  obtain ⟨Q,q,hq,hm⟩ := hU.2
  let row := pairNumerical (numericalConstant n) numericalIdentity
  have hrow : NumericalComputes row (fun s => Nat.pair n s) :=
    (numericalConstant_computes n).pair numericalIdentity_computes
  refine ⟨numericalCompose P row,numericalCompose Q row,fun s => p (Nat.pair n s),q n,
    hp.comp hrow,hv n,hn n,?_,hm n⟩
  simpa only [Nat.unpair_pair] using hq.comp hrow

theorem empty_schnorr_test : SchnorrTest (fun _ => (∅ : Set (ℕ → Bool))) := by
  obtain ⟨P,Q,p,q,hp,hv,hn,hq,hm⟩ := computablyMeasured_empty
  have hopen : UniformlyOpen (fun _ => (∅ : Set (ℕ → Bool))) := by
    refine ⟨numericalCompose P (numericalProjectionTerm false),fun z => p z.unpair.2,
      ?_,fun n => ?_,fun n => ?_⟩
    · simpa only [Bool.false_eq_true,ite_false] using hp.comp (projection_computes false)
    · simpa only [Nat.unpair_pair] using hv
    · simpa only [Nat.unpair_pair] using hn
  refine ⟨⟨hopen,fun n => by simp⟩,?_⟩
  refine ⟨numericalCompose Q (numericalProjectionTerm false),fun _ => q,?_,fun _ => hm⟩
  simpa only [Bool.false_eq_true,ite_false] using hq.comp (projection_computes false)

theorem UniformlyOpen.exists_numerical_index {U : ℕ → Set (ℕ → Bool)} (hU : UniformlyOpen U) :
    ∃ e, ∃ p : ℕ → ℕ, NumericalComputes (Term.closedProgram e) p ∧
      ∀ n, U n = namedOpen (fun s => p (Nat.pair n s)) := by
  obtain ⟨P,p,hp,hv,hn⟩ := hU
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hp.1
  exact ⟨e,p,he ▸ hp,hn⟩

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: lemma
  title: Countability of Schnorr tests
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    For each test, choose an index of a closed numerical program enumerating its open table.
    If the same index is chosen for two tests, uniqueness of numerical outputs makes their tables equal at
    every input, and hence their open sets agree in every row. Thus the chosen indices give an injection into
    $\NN$. The family is nonempty: the constant empty test is a Schnorr test, with constant zero open entries
    and constant rational zero measure names. A countable nonempty family has an enumeration by $\NN$.
    Choosing indices in this argument does not provide a decision procedure for whether an arbitrary program
    is a valid Schnorr test.
-/
theorem countable_schnorr_tests : Countable {U : ℕ → Set (ℕ → Bool) // SchnorrTest U} := by
  classical
  let code (U : {U : ℕ → Set (ℕ → Bool) // SchnorrTest U}) : ℕ :=
    U.property.1.1.exists_numerical_index.choose
  apply Function.Injective.countable (f := code)
  intro U V h
  obtain ⟨p,hp,hn⟩ := U.property.1.1.exists_numerical_index.choose_spec
  obtain ⟨r,hr,hm⟩ := V.property.1.1.exists_numerical_index.choose_spec
  change NumericalComputes (Term.closedProgram (code U)) p at hp
  change NumericalComputes (Term.closedProgram (code V)) r at hr
  rw [h] at hp
  have he : p = r := funext (fun k => numeral_output_unique (hp.2 k) (hr.2 k))
  apply Subtype.ext
  funext n
  rw [hn,hm,he]

/-- The sequence exists classically. Validity of the enumerated tests is not decidable. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: lemma
  title: Countability of Schnorr tests
-/
theorem exists_schnorr_test_enumeration :
    ∃ T : ℕ → ℕ → Set (ℕ → Bool), (∀ e, SchnorrTest (T e)) ∧
      ∀ U, SchnorrTest U → ∃ e, T e = U := by
  let := countable_schnorr_tests
  let : Nonempty {U : ℕ → Set (ℕ → Bool) // SchnorrTest U} := ⟨⟨_,empty_schnorr_test⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat {U : ℕ → Set (ℕ → Bool) // SchnorrTest U}
  refine ⟨fun e => (f e).val,fun e => (f e).property,fun U hU => ?_⟩
  obtain ⟨e,he⟩ := hf ⟨U,hU⟩
  exact ⟨e,congrArg Subtype.val he⟩

theorem computable_point_mem_universal {X : AlphaTerm} {x : ℕ → Bool}
    (hx : NumericalComputes X (fun k => (x k).toNat)) (n : ℕ) : x ∈ universalOpen n := by
  have hn : ¬ MLRandom x := fun h => not_schnorrRandom_of_computable hx h.schnorrRandom
  have hi : x ∈ ⋂ k, universalOpen k := by
    by_contra h
    exact hn ((mlRandom_iff_avoids_universal x).mpr h)
  exact mem_iInter.mp hi n

theorem measured_closed_support {K : Set (ℕ → Bool)} (hK : ComputablyMeasuredOpen Kᶜ)
    (hpos : 0 < fairCoinProduct.real K) :
    ∃ X : AlphaTerm, ∃ x : ℕ → Bool, NumericalComputes X (fun k => (x k).toNat) ∧
      x ∈ K ∧ ∀ k, 0 < fairCoinProduct.real (K ∩ cyl (seqPrefix x k)) := by
  obtain ⟨P,Q,p,q,hp,hv,he,hq,hm⟩ := hK
  have he' : (namedOpen p)ᶜ = K := by rw [← he,compl_compl]
  rw [he] at hm
  obtain ⟨X,x,hx,hout,hlocal⟩ := exists_computable_closed_support hp hv q hq hm (he' ▸ hpos)
  refine ⟨X,x,hx,?_,fun k => ?_⟩
  · rw [← he']; exact hout
  · simpa only [sdiff_eq_compl_inter,he'] using hlocal k

/-- One finite refinement avoids one test row and enters a prescribed universal row. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: lemma
  title: Refining a positive closed set
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    First compute an integer $n$ with $2^{-n}<\mu(K)/2$.
    Let $Q$ compute a fast Cauchy name $a$ of the measure of the open complement, and write
    $r_s:=q_{a(s)}$. Search for the first $s$ with
    $$r_s+2\cdot2^{-s}<1,$$
    and put $n:=s+1$. The search terminates because $r_s\to1-\mu(K)<1$.
    The Cauchy error bound gives $1-\mu(K)\le r_s+2^{-s}$, hence
    $$2^{-s}<\mu(K),\qquad 2^{-n}<\mu(K)/2.$$
    To write the search as a lambda term, put $c_1:=\RationalCode{1}{0}{0}$ and use
    $$\begin{aligned}
    A&:=\lambdaab{s}{\LambdaRationalAdd(\LambdaNumericPair\,(Qs)\,(\LambdaDyadic\,s))},\\
    B&:=\lambdaab{s}{\LambdaRationalAdd(\LambdaNumericPair\,(As)\,(\LambdaDyadic\,s))},\\
    T&:=\lambdaab{s}{\LambdaRationalLess(\LambdaNumericPair\,(Bs)\,\ChurchNumeral{c_1})},\\
    J&:=\LambdaResultSearch\,
     (\lambdaab{s}{\LambdaZeroTest\,(Ts)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,\LambdaSucc.
    \end{aligned}$$
    The rational comparison succeeds at the stated stage and $J\to_\beta^*\ChurchNumeral{n}$.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Set $C:=\SetDifference{K}{U_n}$. Then
    $$\mu(C)\ge\mu(K)-\mu(U_n)\ge\mu(K)-2^{-n}>\mu(K)/2>0.$$
    Its complement is the union of the open complement of $K$ and $U_n$.
    Both have computable open and measure names, so the finite-union proposition makes $C$ effectively closed
    with computable measure. The row programs for $U_n$ are obtained by substituting the computed numeral for
    the row argument of the two uniform Schnorr-test programs.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Apply the computable-support-point theorem to $C$. It gives a computable point $y\in C$ with
    $$\mu(C\cap\cyl{\restrict{y}{k}})>0\qquad(k\in\NN).$$
    Every computable point fails Schnorr randomness, hence also Martin-Löf randomness.
    By universality, $y\in V_e$. The cylinder-search lemma computes a binary word $w$ with
    $y\in\cyl{w}\IncludedIn V_e$. Since $w=\restrict{y}{|w|}$, the set
    $$L:=C\cap\cyl{w}$$
    has positive measure. It is effectively closed with computable measure by the cylinder-complement lemma.
    It is contained in $K\cap V_e$ and disjoint from $U_n$, as required.
-/
theorem schnorr_closed_refinement {K : Set (ℕ → Bool)} (hK : ComputablyMeasuredOpen Kᶜ)
    (hpos : 0 < fairCoinProduct.real K) {U : ℕ → Set (ℕ → Bool)} (hU : SchnorrTest U) (e : ℕ) :
    ∃ L : Set (ℕ → Bool), ComputablyMeasuredOpen Lᶜ ∧ 0 < fairCoinProduct.real L ∧
      L ⊆ K ∧ L ⊆ universalOpen e ∧ ∃ n, Disjoint L (U n) := by
  have hKdata := hK
  obtain ⟨P,Q,p,q,hp,hv,hnames,hq,hm⟩ := hKdata
  have hclosed : IsClosed K := by simpa only [compl_compl] using hK.isOpen.isClosed_compl
  have hmass : realRepresentation.toFun q = 1-fairCoinProduct.real K := by
    rw [hm,measureReal_compl hclosed.measurableSet,probReal_univ]
  have hlt : realRepresentation.toFun q < 1 := by rw [hmass]; linarith
  obtain ⟨_,n,_hrow,hn⟩ := positiveComplementRowProgram_finds q hq hlt
  rw [hmass] at hn
  have hsmall : fairCoinProduct.real (U n) < fairCoinProduct.real K/2 := by
    have hb := hU.1.2 n
    linarith
  let C := K \ U n
  have hC : ComputablyMeasuredOpen Cᶜ := by
    simpa only [C,sdiff_eq_compl_inter,compl_inter,compl_compl,union_comm] using
      hK.union (hU.computablyMeasured_row n)
  have hCpos : 0 < fairCoinProduct.real C := by
    have hb := le_measureReal_sdiff (μ := fairCoinProduct) (s₁ := K) (s₂ := U n)
    dsimp [C]
    linarith
  obtain ⟨X,x,hx,hxin,hlocal⟩ := measured_closed_support hC hCpos
  obtain ⟨P,p,hp,hv,hnames⟩ := universalOpen_uniform
  let row := pairNumerical (numericalConstant e) numericalIdentity
  have hrow : NumericalComputes row (fun s => Nat.pair e s) :=
    (numericalConstant_computes e).pair numericalIdentity_computes
  have hmem : x ∈ namedOpen (fun s => p (Nat.pair e s)) := by
    rw [← hnames e]
    exact computable_point_mem_universal hx e
  obtain ⟨_,w,_hprogram,hw,hsub⟩ := computable_point_cylinder (hp.comp hrow) (hv e) hx hmem
  rw [← hnames e] at hsub
  have hpre := seqPrefix_eq_of_mem_cyl hw
  refine ⟨C ∩ cyl w,computablyMeasured_complement_inter_cylinder hC w,?_,?_,?_,n,?_⟩
  · simpa only [hpre] using hlocal w.length
  · exact inter_subset_left.trans sdiff_subset
  · exact inter_subset_right.trans hsub
  · exact Set.disjoint_left.mpr (fun y hy hu => hy.1.2 hu)


/-- Compactness closes the countable construction; the resulting point need not be computable. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Schnorr randomness does not imply Martin-Löf randomness
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Fix a set-theoretic enumeration $\Sequence{\Sequence{U^e_n}{n\in\NN}}{e\in\NN}$ of all Schnorr tests.
    Starting with $K_0:=\CantorSpace$, apply the refinement lemma recursively to obtain effectively closed sets
    of positive computable measure and integers $n_e$ such that
    $$K_{e+1}\IncludedIn K_e\cap V_e,\qquad K_{e+1}\cap U^e_{n_e}=\emptyset.$$
    Each set is nonempty and closed in compact Cantor space, and the sets decrease.
    Compactness gives a point
    $$x\in\bigcap_e K_e.$$
    For every $e$, this point is outside $U^e_{n_e}$, so it passes every Schnorr test.
    On the other hand, $x\in K_{e+1}\IncludedIn V_e$ for every $e$, hence $x$ fails the universal Martin-Löf test.
    Thus it has precisely the asserted two randomness properties.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    The finite refinement uses the lambda programs given above for row selection, finite-union measure,
    support points, and cylinder search. The enumeration of valid tests and the choice of a point in the infinite
    intersection are set-theoretic steps. In particular, the argument does not compute the final point;
    no Schnorr-random point is computable.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    \termdefine{Schnorr randomness} tightens the measure side of the test [@Schnorr1971]. A \termdefine{Schnorr test} is a
    Martin-Löf test $\Sequence{U_n}{n\in\omega}$ for which the real number $\mu(U_n)$ is computable uniformly in $n$. Every
    Martin-Löf random
    point is Schnorr random. The converse fails already for fair-coin measure on Cantor space. The distinction
    matters because Schnorr randomness treats the measure of
    the test itself as part of the effective data, matching the computable-analysis principle that negative information
    should be supplied with a usable modulus rather than only an existence proof.
-/
theorem exists_schnorrRandom_not_mlRandom :
    ∃ x : ℕ → Bool, SchnorrRandom x ∧ ¬ MLRandom x := by
  classical
  obtain ⟨T,hT,hcover⟩ := exists_schnorr_test_enumeration
  let Condition := {K : Set (ℕ → Bool) // ComputablyMeasuredOpen Kᶜ ∧ 0 < fairCoinProduct.real K}
  have hstep (e : ℕ) (K : Condition) := schnorr_closed_refinement K.property.1 K.property.2 (hT e) e
  choose F hFdata hFpos hFsub hFin hFavoid using hstep
  have hinit : ComputablyMeasuredOpen (Set.univ : Set (ℕ → Bool))ᶜ := by
    simpa only [compl_univ] using computablyMeasured_empty
  let C : ℕ → Condition := Nat.rec ⟨Set.univ,hinit,by simp⟩
    (fun e K => ⟨F e K,hFdata e K,hFpos e K⟩)
  have hsucc (e : ℕ) : (C (e+1)).val = F e (C e) := rfl
  have hsub (e : ℕ) : (C (e+1)).val ⊆ (C e).val := by rw [hsucc]; exact hFsub e (C e)
  have hclosed (e : ℕ) : IsClosed (C e).val := by
    simpa only [compl_compl] using (C e).property.1.isOpen.isClosed_compl
  have hnonempty (e : ℕ) : (C e).val.Nonempty := by
    by_contra h
    have hp := (C e).property.2
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hp
    simp at hp
  have hcompact : IsCompact (C 0).val := isCompact_univ
  obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun e => (C e).val) hsub hnonempty hcompact hclosed
  have hmem (e : ℕ) : x ∈ F e (C e) := by
    rw [← hsucc]
    exact mem_iInter.mp hx (e+1)
  refine ⟨x,?_,?_⟩
  · intro U hU hfail
    obtain ⟨e,rfl⟩ := hcover U hU
    obtain ⟨n,hn⟩ := hFavoid e (C e)
    exact Set.disjoint_left.mp hn (hmem e) (mem_iInter.mp hfail n)
  · intro hML
    have hfail : x ∈ ⋂ e, universalOpen e := mem_iInter.mpr (fun e => hFin e (C e) (hmem e))
    exact (mlRandom_iff_avoids_universal x).mp hML hfail

end PolishSpaceBook.LambdaRandomness
