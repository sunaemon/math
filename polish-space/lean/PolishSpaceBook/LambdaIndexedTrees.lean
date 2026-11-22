module

public import PolishSpaceBook.LambdaPairTrees
public import PolishSpaceBook.LambdaRelativeIndices
public import PolishSpaceBook.LambdaOracleOutputSearch

@[expose] public section

/-! # A total family of pair trees from arbitrary lambda indices

At length n, inspect the first n paired prefix/certificate trials. A node is
removed only after a finite certificate proves output zero on one of its
prefixes. The index need not decide a total predicate. Valid decision indices
preserve closed bodies and projections, not necessarily finite nodes or ranks.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set
namespace NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def uniformCandidateBody (O Z : AlphaTerm) : AlphaTerm :=
  app (app (app (app oracleOutputCandidateTerm O)
    (app (numericalProjectionTerm true) Z))
    (app (numericalProjectionTerm true) (app (numericalProjectionTerm false) Z)))
    (app (numericalProjectionTerm false) (app (numericalProjectionTerm false) Z))

theorem uniformCandidateBody_subst (O Z W : AlphaTerm) (x : ℕ) :
    (uniformCandidateBody O Z).subst x W =
      uniformCandidateBody (O.subst x W) (Z.subst x W) := by
  simp only [uniformCandidateBody,subst_app,subst_closed _ _ _ oracleOutputCandidateTerm_closed,
    subst_closed _ _ _ (projection_computes true).1,subst_closed _ _ _ (projection_computes false).1]

/-- One candidate tester, with its program index supplied as part of the input. -/
def uniformCandidateProgram : AlphaTerm := lam 70 (lam 71 (uniformCandidateBody (var 70) (var 71)))

theorem uniformCandidateProgram_closed : uniformCandidateProgram.Closed := by
  unfold uniformCandidateProgram uniformCandidateBody Closed
  simp only [fv_lam,fv_app,fv_var,(show oracleOutputCandidateTerm.fv = ∅ from oracleOutputCandidateTerm_closed),
    (show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1),
    (show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1)]
  decide

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Fix a parameter $\varepsilon$ and enumerate the closed lambda programs as $P_e$ using their syntax codes.
    The finite-certificate checker in §{sec:lambda-input-universal-evaluation} gives a total zero/one test
    $C(e,a,b)$: it returns one exactly when a certificate within bound $b$ proves that $P_e$, with parameter
    $\varepsilon$, returns zero on input code $a$. Every actual zero output has such a certificate for some bound.
    This test is uniform in all three numerical arguments and uses the same fixed parameter.
-/
theorem uniformCandidateProgram_computes (ε : ℕ → ℕ) :
    LambdaRelative.Computes ε uniformCandidateProgram
      (fun z : ℕ => if Term.oracleOutputCandidate ε z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 then 1 else 0) := by
  refine ⟨uniformCandidateProgram_closed,fun z => ?_⟩
  have h₁ : Beta (app uniformCandidateProgram (var 0))
      (lam 71 (uniformCandidateBody (var 0) (var 71))) := by
    have he : (lam 71 (uniformCandidateBody (var 70) (var 71))).subst 70 (var 0) =
        lam 71 (uniformCandidateBody (var 0) (var 71)) := by
      rw [subst_lam_fresh _ _ 71 70 (by decide) (by simp [fv_var]),uniformCandidateBody_subst]
      simp [subst_var]
    rw [← he]
    exact Beta.contract 70 _ _
  have h₂ : Beta (app (lam 71 (uniformCandidateBody (var 0) (var 71))) (numeral z))
      (uniformCandidateBody (var 0) (numeral z)) := by
    have he : (uniformCandidateBody (var 0) (var 71)).subst 71 (numeral z) =
        uniformCandidateBody (var 0) (numeral z) := by
      simp [uniformCandidateBody_subst,subst_var]
    rw [← he]
    exact Beta.contract 71 _ _
  have hleft := (projection_computes true).2 z
  have hmid := (beta_steps_app_right (numericalProjectionTerm true) ((projection_computes false).2 z)).trans
    ((projection_computes true).2 z.unpair.2)
  have hright := (beta_steps_app_right (numericalProjectionTerm false) ((projection_computes false).2 z)).trans
    ((projection_computes false).2 z.unpair.2)
  exact (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
    ((oracle_steps_app (oracle_steps_app (oracle_steps_app_right _ (beta_steps_oracle hleft))
      (beta_steps_oracle hmid)) (beta_steps_oracle hright)).trans
      (oracleOutputCandidateTerm_apply ε z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2))

/-- Truncate both encoded words at the supplied length. -/
def takePairTerm : AlphaTerm :=
  pairNumerical
    (numericalCompose listTakeTerm (pairNumerical
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
      (numericalProjectionTerm false)))
    (numericalCompose listTakeTerm (pairNumerical
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))
      (numericalProjectionTerm false)))

def takePairCode (e n : ℕ) : ℕ := Nat.pair
  (NatListCode.encode ((NatListCode.decode e.unpair.1).take n))
  (NatListCode.encode ((NatListCode.decode e.unpair.2).take n))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The finite output-candidate checker is total even when the indexed program is partial. Supply its program
    index as data together with the node code. To truncate a pair of word codes, expand
    $$\begin{aligned}
    \LambdaTermName{truncatePair}(w,j):=\LambdaNumericPair\,
     &\bigl(\LambdaListTake\,(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,j)\bigr)\\
     &\bigl(\LambdaListTake\,(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,j)\bigr).
    \end{aligned}$$
    On input $\NatPair{w}{j}$, the corresponding closed numerical term computes the code of the pair of
    length-$j$ truncations. Both projections, both prefix extractions, and the final pairing are total.
-/
theorem takePair_computes : NumericalComputes takePairTerm (fun z => takePairCode z.unpair.1 z.unpair.2) := by
  have h₁ := listTake_computes.comp
    (((projection_computes true).comp (projection_computes true)).pair (projection_computes false))
  have h₂ := listTake_computes.comp
    (((projection_computes false).comp (projection_computes true)).pair (projection_computes false))
  simpa only [takePairTerm,takePairCode,Nat.unpair_pair,Bool.false_eq_true,ite_false,ite_true] using h₁.pair h₂

/-- Input is ((e,node),(depth,bound)); the candidate output is zero. -/
def rejectionInputTerm : AlphaTerm :=
  let a := numericalProjectionTerm true
  let b := numericalProjectionTerm false
  pairNumerical (numericalCompose a a)
    (pairNumerical (numericalCompose takePairTerm
      (pairNumerical (numericalCompose b a) (numericalCompose a b)))
      (pairNumerical (numericalConstant 0) (numericalCompose b b)))

theorem rejectionInput_computes : NumericalComputes rejectionInputTerm
    (fun z => Nat.pair z.unpair.1.unpair.1
      (Nat.pair (takePairCode z.unpair.1.unpair.2 z.unpair.2.unpair.1)
        (Nat.pair 0 z.unpair.2.unpair.2))) := by
  have a := projection_computes true
  have b := projection_computes false
  simpa only [rejectionInputTerm,Nat.unpair_pair,Bool.false_eq_true,ite_false,ite_true] using
    (a.comp a).pair ((takePair_computes.comp ((b.comp a).pair (a.comp b))).pair
      ((numericalConstant_computes 0).pair (b.comp b)))

def rejectionTest (ε : ℕ → ℕ) (e node i : ℕ) : Bool :=
  Term.boundedInputTest ε (Term.oracleProgramInput e (takePairCode node i.unpair.1))
    (Term.churchNumeral 0) i.unpair.2

def passingTrialProgram : AlphaTerm :=
  mapOutputProgram reverseZeroTerm (reindexProgram uniformCandidateProgram rejectionInputTerm)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Decode a trial input as $v=\NatPair{\NatPair{e}{w}}{\NatPair{j}{r}}$, using the four compositions of numerical
    projections, and abbreviate these four projected terms by $e,w,j,r$ inside the following body:
    $$\begin{aligned}
    \LambdaTermName{rejectCandidate}(o,v)&:=\LambdaQueryOutputCandidate\,o\,e\,\LambdaTermName{truncatePair}(w,j)
      \,\bigl(\LambdaNumericPair\,\ChurchNumeral{0}\,r\bigr),\\
    \LambdaTermName{acceptTrial}&:= \lambdaab{o}{ \lambdaab{v}{ \LambdaZeroTest\,
    \LambdaTermName{rejectCandidate}(o,v)\, \ChurchNumeral{1}\, \ChurchNumeral{0}}}.
    \end{aligned}$$
    Thus $\LambdaTermName{rejectCandidate}$ returns one exactly when the trial certifies output zero, and
    $\LambdaTermName{acceptTrial}$ reverses that bit. The universal
    candidate test makes the program independent of the supplied index. Each trial terminates at every parameter.
-/
theorem passingTrial_computes (ε : ℕ → ℕ) :
    LambdaRelative.Computes ε passingTrialProgram
      (fun z : ℕ => if rejectionTest ε z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2 then 0 else 1) := by
  have h := ((uniformCandidateProgram_computes ε).reindex rejectionInput_computes).map reverseZero_computes
  unfold passingTrialProgram
  convert h using 1
  funext z
  simp only [rejectionTest,Term.oracleOutputCandidate,Nat.unpair_pair]
  split_ifs <;> simp_all

/-- Decode the family input (index,pair of words) and count the first word's length. -/
def familyLengthTerm : AlphaTerm := numericalCompose listLengthTerm
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))

theorem familyLength_computes : NumericalComputes familyLengthTerm
    (fun z => (NatListCode.decode z.unpair.2.unpair.1).length) := by
  exact listLength_computes.comp ((projection_computes true).comp (projection_computes false))

def familyLengthEqualityTerm : AlphaTerm := numericalCombine equalityTerm familyLengthTerm
  (numericalCompose listLengthTerm (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))

theorem familyLengthEquality_computes : NumericalComputes familyLengthEqualityTerm
    (fun z => if (NatListCode.decode z.unpair.2.unpair.1).length =
      (NatListCode.decode z.unpair.2.unpair.2).length then 1 else 0) := by
  exact familyLength_computes.combine
    (listLength_computes.comp ((projection_computes false).comp (projection_computes false)))
    equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the family input $z=\NatPair{e}{w}$, let
    $$\begin{aligned}
    \LambdaTermName{firstLength}(z)&:=\LambdaListLength(\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z)),\\
    \LambdaTermName{secondLength}(z)&:=\LambdaListLength(\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z)),\\
    \LambdaTermName{sameLength}(z)&:=\LambdaEqual\,\LambdaTermName{firstLength}(z)\,\LambdaTermName{secondLength}(z),\\
    \LambdaTermName{indexedTree}&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,\LambdaTermName{sameLength}(z)\,
     \bigl( \LambdaRelativeProduct{ \LambdaTermName{acceptTrial}}\,o\,( \LambdaNumericPair\,z\,
    \LambdaTermName{firstLength}(z)) \bigr)}}.
    \end{aligned}$$
    As throughout, expand the abbreviations before abstraction and choose distinct fresh binders.
    For a fixed parameter $\varepsilon$, define
    $T_e$ here as the set of equal-length pairs $\Pair{s}{t}$ for which the reversed trial
    $\LambdaTermName{acceptTrial}$ returns one at every
    $i<\Length{s}$, on input $\NatPair{\NatPair{e}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}}{i}$.
-/
def indexedFamilyProgram : AlphaTerm :=
  mapOutputProgram (mulNumerical (numericalProjectionTerm true) (numericalProjectionTerm false))
    (pairOutputProgram (liftNumericalProgram familyLengthEqualityTerm)
      (reindexProgram (relativeProductProgram passingTrialProgram)
        (pairNumerical numericalIdentity familyLengthTerm)))

end NamedLambda.AlphaTerm
namespace LambdaTree
local instance indexedTreeListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance indexedTreePairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Delayed rejection of a finite pair, with finitely many tests at every index. -/
def indexedNodes (ε : ℕ → ℕ) (e : ℕ) : Set (List ℕ × List ℕ) :=
  {z | z.1.length = z.2.length ∧ ∀ i < z.1.length,
    rejectionTest ε e (Encodable.encode z) i = false}

local instance indexedNodesMembership (ε : ℕ → ℕ) (e : ℕ) (z : List ℕ × List ℕ) :
    Decidable (z ∈ indexedNodes ε e) :=
  inferInstanceAs (Decidable (z.1.length = z.2.length ∧ ∀ i < z.1.length,
    rejectionTest ε e (Encodable.encode z) i = false))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For a finite pair $(s,t)$, require $|s|=|t|$ and put $n=|s|$. For each $i<n$, decode $i=\NatPair{j}{b}$ and
    perform the test
    $$C\!\left(e,\NatPair{\LambdaListCode{\restrict{s}{j}}}{\LambdaListCode{\restrict{t}{j}}},b\right).$$
    Put $(s,t)\in T_e$ exactly when all these answers are zero. There are only finitely many terminating tests,
    so one program decides the family. The empty pair passes because there are no trials. The numerical pairing
    satisfies $j\le i$. On truncation to length $m\le n$, every trial $i<m$ therefore examines the same pair of
    prefixes as before. Thus membership is preserved by truncation, for every index, including indices of partial
    programs.
-/
theorem indexedNodes_downward (ε : ℕ → ℕ) (e : ℕ)
    {z : List ℕ × List ℕ} (hz : z ∈ indexedNodes ε e) (n : ℕ) :
    (z.1.take n,z.2.take n) ∈ indexedNodes ε e := by
  refine ⟨by simp [hz.1],fun i hi => ?_⟩
  have hi' : i < z.1.length := by simp only [List.length_take] at hi; omega
  have hin : i < n := by simp only [List.length_take] at hi; omega
  have hjn : i.unpair.1 ≤ n := (Nat.unpair_left_le i).trans hin.le
  simpa [rejectionTest,takePairCode,Encodable.encode,List.take_take,min_eq_left hjn] using hz.2 i hi'

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Uniform indexed-tree decider
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The candidate checker and the truncation program give precisely the rejection test used in the definition of
    $T_e$. The relative bounded product of $\Length{s}$ reversed bits is one exactly when none of
    the first $\Length{s}$ trials
    rejects. Multiplication by the length-equality bit enforces synchronization. At length zero the product is
    one, with no trial evaluated. Each component is total on its supplied numerical inputs, so this also proves
    termination without any hypothesis on the indexed program.
-/
theorem indexedFamily_computes (ε : ℕ → ℕ) :
    LambdaRelative.Computes ε indexedFamilyProgram (fun z : ℕ =>
      if ((NatListCode.decode z.unpair.2.unpair.1,NatListCode.decode z.unpair.2.unpair.2) ∈ indexedNodes ε z.unpair.1)
      then 1 else 0) := by
  classical
  have hp := ((passingTrial_computes ε).boundedProduct).reindex
    (numericalIdentity_computes.pair familyLength_computes)
  have h := ((LambdaRelative.ofNumerical familyLengthEquality_computes ε).pair hp).map
    ((projection_computes true).mul (projection_computes false))
  unfold indexedFamilyProgram
  convert h using 1
  funext z
  simp only [Nat.unpair_pair,id_eq]
  let t : ℕ → ℕ := fun w => if rejectionTest ε w.unpair.1.unpair.1 w.unpair.1.unpair.2 w.unpair.2 then 0 else 1
  have hb := boundedProduct_zero_or_one t z (NatListCode.decode z.unpair.2.unpair.1).length
    (fun i => by dsimp [t]; split_ifs <;> simp)
  have he : boundedProduct t z (NatListCode.decode z.unpair.2.unpair.1).length ≠ 0 ↔
      ∀ i < (NatListCode.decode z.unpair.2.unpair.1).length,
        rejectionTest ε z.unpair.1 z.unpair.2 i = false := by
    rw [boundedProduct_ne_zero]
    simp [t]
  change (if _ then 1 else 0) = (if _ then 1 else 0) * boundedProduct t z _
  simp only [indexedNodes,Set.mem_ofPred_eq,Encodable.encode,NatListCode.encode_decode,Nat.pair_unpair]
  by_cases hl : (NatListCode.decode z.unpair.2.unpair.1).length =
      (NatListCode.decode z.unpair.2.unpair.2).length
  · simp only [hl,ite_true,true_and,one_mul]
    rw [hl] at hb he
    by_cases hall : ∀ i < (NatListCode.decode z.unpair.2.unpair.2).length,
        rejectionTest ε z.unpair.1 z.unpair.2 i = false
    · rw [ite_eq_left hall,hb.resolve_left (he.mpr hall)]
    · have hz : boundedProduct t z (NatListCode.decode z.unpair.2.unpair.2).length = 0 :=
        not_not.mp (fun hne => hall (he.mp hne))
      rw [ite_eq_right hall,hz]
  · simp [hl]

def indexedTree (ε : ℕ → ℕ) (e : ℕ) : PairTree ε where
  tree := indexedNodes ε e
  synchronized := fun _ h => h.1
  downward := fun _ h n => indexedNodes_downward ε e h n
  decidable := by
    have hF := indexedFamily_computes ε
    have hcode := (numericalConstant_computes e).pair numericalIdentity_computes
    refine ⟨reindexProgram indexedFamilyProgram (pairNumerical (numericalConstant e) numericalIdentity),
      reindexProgram_closed hF.1 hcode.1,fun z => ⟨?_,?_⟩⟩
    all_goals
      intro hz
      have h := reindexProgram_runs hF.1 hcode.1 ε (Encodable.encode z) _ _
        (hcode.2 _) (hF.2 (Nat.pair e (Encodable.encode z)))
      simpa [Encodable.encode,hz] using h

theorem empty_mem_indexedTree (ε : ℕ → ℕ) (e : ℕ) :
    ([],[]) ∈ (indexedTree ε e).tree := by
  simp [indexedTree,indexedNodes]

/-- Failure ever to return zero does not make the indexed tree partial. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The construction delays rejection; it preserves the body and projection of a correctly decided tree, rather than
    its individual finite nodes or well-founded rank. If a program never returns zero on any numerical input,
    its tree is the full synchronized tree, since no rejecting certificate exists. This family therefore requires
    no decision of totality and does not enumerate the characteristic functions of all recursive trees.
-/
theorem indexedTree_of_no_zero (ε : ℕ → ℕ) (e : ℕ)
    (he : ∀ n, ¬ OracleRuns ε (Term.closedProgram e) n 0) :
    (indexedTree ε e).tree = (fullPairTree ε).tree := by
  ext z
  change (z.1.length = z.2.length ∧ _) ↔ z.1.length = z.2.length
  constructor
  · exact And.left
  · intro hz
    refine ⟨hz,fun i _ => ?_⟩
    by_contra hi
    have ht := Bool.eq_true_of_not_eq_false hi
    exact he _ ((oracle_outputTest_exists_iff ε e _ 0).mp ⟨i.unpair.2,ht⟩)

/-- One program decides the whole family, including indices of partial programs. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Uniform pair-tree presentations
-/
theorem indexedTree_family_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (indexedTree ε z.1).tree) := by
  have h := indexedFamily_computes ε
  refine ⟨indexedFamilyProgram,h.1,fun z => ⟨?_,?_⟩⟩
  all_goals
    intro hz
    rcases z with ⟨e,s,t⟩
    simp only [indexedTree] at hz
    have hr := h.2 (Nat.pair e (Nat.pair (NatListCode.encode s) (NatListCode.encode t)))
    change OracleRuns ε indexedFamilyProgram (Nat.pair e (Nat.pair (NatListCode.encode s) (NatListCode.encode t))) _
    simpa [indexedTree,hz] using hr

/-- A deciding index is a genuine closed lambda decision program on the book's codes. -/
def TreeIndex (ε : ℕ → ℕ) (e : ℕ) (T : Set (List ℕ × List ℕ)) : Prop :=
  LambdaRelative.Decides ε (Term.closedProgram e) (· ∈ T)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Now suppose $P_e$ decides $T$. If $(p,q)\in[T]$, every tested prefix has answer one from the decider, so no
    sound certificate can prove answer zero; all finite pairs on this branch belong to $T_e$. Conversely, if a
    prefix of length $j$ fails membership in $T$, its decision returns zero. Choose a certificate bound $b$, put
    $i=\NatPair{j}{b}$, and take $n=i+1$. The length-$n$ pair fails trial $i$, so $(p,q)\notin[T_e]$. This proves
    both body inclusions and hence equality of projections. Every relative pair tree has a deciding index, and
    every index in the displayed family gives a relative pair tree, proving the final assertion.
-/
theorem pairTreeBody_indexedTree (ε : ℕ → ℕ) (e : ℕ) (T : Set (List ℕ × List ℕ))
    (he : TreeIndex ε e T) : pairTreeBody (indexedTree ε e).tree = pairTreeBody T := by
  ext p
  constructor
  · intro hp j
    by_contra hj
    have hv := (he.2 (seqPrefix p.1 j,seqPrefix p.2 j)).2 hj
    obtain ⟨b,hb⟩ := (oracle_outputTest_exists_iff ε e _ 0).mpr hv
    let i := Nat.pair j b
    let n := i+1
    have hjn : j ≤ n := (Nat.left_le_pair j b).trans (Nat.le_succ _)
    have hbad := (hp n).2 i (by simp [n,seqPrefix_length])
    have hc : rejectionTest ε e (Encodable.encode (seqPrefix p.1 n,seqPrefix p.2 n)) i = true := by
      simpa [rejectionTest,takePairCode,Encodable.encode,i,seqPrefix_take_of_le _ hjn] using hb
    simp_all
  · intro hp n
    refine ⟨by simp [seqPrefix_length],fun i hi => ?_⟩
    have hjn : i.unpair.1 ≤ n := (Nat.unpair_left_le i).trans (by simpa [seqPrefix_length] using hi.le)
    by_contra hbad
    have hb : rejectionTest ε e (Encodable.encode (seqPrefix p.1 n,seqPrefix p.2 n)) i = true :=
      Bool.eq_true_of_not_eq_false hbad
    have hc : Term.boundedInputTest ε
        (Term.oracleProgramInput e (Encodable.encode (seqPrefix p.1 i.unpair.1,seqPrefix p.2 i.unpair.1)))
        (Term.churchNumeral 0) i.unpair.2 = true := by
      simpa [rejectionTest,takePairCode,Encodable.encode,seqPrefix_take_of_le _ hjn] using hb
    have hzero := (oracle_outputTest_exists_iff ε e _ 0).mp ⟨_,hc⟩
    have hone := (he.2 (seqPrefix p.1 i.unpair.1,seqPrefix p.2 i.unpair.1)).1 (hp i.unpair.1)
    have := hzero.output_unique hone
    omega

theorem pairTreeProjection_indexedTree (ε : ℕ → ℕ) (e : ℕ) (T : Set (List ℕ × List ℕ))
    (he : TreeIndex ε e T) : pairTreeProjection (indexedTree ε e).tree = pairTreeProjection T := by
  unfold pairTreeProjection
  rw [pairTreeBody_indexedTree ε e T he]

theorem exists_treeIndex (ε : ℕ → ℕ) (T : PairTree ε) : ∃ e, TreeIndex ε e T.tree :=
  T.decidable.exists_index

def indexedProjection (ε : ℕ → ℕ) (e : ℕ) : Set (ℕ → ℕ) :=
  pairTreeProjection (indexedTree ε e).tree

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Uniform pair-tree presentations
-/
theorem projected_iff_index (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    Projected ε A ↔ ∃ e, A = indexedProjection ε e := by
  constructor
  · rintro ⟨T,rfl⟩
    obtain ⟨e,he⟩ := exists_treeIndex ε T
    exact ⟨e,(pairTreeProjection_indexedTree ε e T.tree he).symm⟩
  · rintro ⟨e,rfl⟩
    exact ⟨indexedTree ε e,rfl⟩

/-- Specialize the actual family decider by a lambda-computed syntax transformation. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Specialization of relative tree families
-/
theorem treeFamily_indices (ε : ℕ → ℕ) (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    ∃ f : ℕ → ℕ, (∃ F, NumericalComputes F f) ∧
      ∀ i, TreeIndex ε (f i) (T i).tree :=
  hT.specialized_indices

/-- The generated tree family itself has a computable family of valid deciding indices. -/
theorem indexedTree_deciding_indices (ε : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, (∃ F, NumericalComputes F f) ∧
      ∀ i, TreeIndex ε (f i) (indexedTree ε i).tree :=
  treeFamily_indices ε (indexedTree ε) (indexedTree_family_decidable ε)

end LambdaTree
end PolishSpaceBook
