module

public import PolishSpaceBook.EffectiveClosedTreeRepresentation
public import PolishSpaceBook.LambdaPairTrees
public import PolishSpaceBook.LambdaEffectiveOpenSets
public import PolishSpaceBook.LambdaInputParameters
public import PolishSpaceBook.LambdaInputStageBounds
public import PolishSpaceBook.LambdaInputPrefixes
public import PolishSpaceBook.LambdaRelativeComposition

@[expose] public section

/-! # Enumerated cylinders and lambda semidecision on Baire names

The trial programs terminate even when the tested program does not. All
queries retain the same fixed parameter. A single closed search program
works on every point, without choosing a new parameter for that point.
-/

noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm

local instance openSemidecisionWordEncoding : Encodable (List ℕ) := NatListCode.encodable

theorem open_computes_changeParameter {α β : Type*} [Encodable α] [Encodable β]
    {ε δ : ℕ → ℕ} {P Q : AlphaTerm} {f : α → β}
    (hP : LambdaRelative.Computes ε P f) (hQ : LambdaRelative.Computes δ Q ε) :
    LambdaRelative.Computes δ (compositionProgram P Q) f :=
  ⟨compositionProgram_closed hP.1 hQ.1,
    fun a => compositionProgram_runs hP.1 hQ.1 (hP.2 a) hQ.2⟩

def openTrialProgram (e : ℕ) (E X : AlphaTerm) : AlphaTerm :=
  relativeComposeProgram (compositionProgram (acceptanceTestProgram e) E)
    (pairOutputProgram
      (reindexProgram (compositionProgram prefixProgram X)
        (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)))
      (liftNumericalProgram
        (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))))

theorem openTrialProgram_computes {ε δ p : ℕ → ℕ} {E X : AlphaTerm}
    (hE : LambdaRelative.Computes δ E ε) (hX : LambdaRelative.Computes δ X p) (e : ℕ) :
    LambdaRelative.Computes δ (openTrialProgram e E X)
      (fun z : ℕ => if acceptanceTest ε e
        (Nat.pair (NatListCode.encode (seqPrefix p z.unpair.2.unpair.1)) z.unpair.2.unpair.2) then 1 else 0) := by
  have hc := open_computes_changeParameter
    (⟨(acceptanceTestProgram_computes e).1, (acceptanceTestProgram_computes e).2 ε⟩ :
      LambdaRelative.Computes ε (acceptanceTestProgram e)
        (fun z => if acceptanceTest ε e z then 1 else 0)) hE
  have hp := open_computes_changeParameter
    (⟨prefixProgram_closed, fun n => prefixProgram_runs p n⟩ :
      LambdaRelative.Computes p prefixProgram (fun n : ℕ => NatListCode.encode (seqPrefix p n))) hX
  have hn := hp.reindex ((projection_computes true).comp (projection_computes false))
  have hb := LambdaRelative.ofNumerical
    ((projection_computes false).comp (projection_computes false)) δ
  simpa only [openTrialProgram, Nat.unpair_pair, Bool.false_eq_true, ite_false, ite_true] using
    hc.comp (hn.pair hb)

/-- Accessors are actual total lambda computations of the original parameter
and point from the supplied name. The output program is fixed before p. -/
theorem effectivelyOpen_semidecision_with_accessors {ε : ℕ → ℕ} {U : Set (ℕ → ℕ)}
    (hU : RelativelyEffectivelyOpen ε U) (δ : (ℕ → ℕ) → (ℕ → ℕ)) (E X : AlphaTerm)
    (hE : ∀ p, LambdaRelative.Computes (δ p) E ε)
    (hX : ∀ p, LambdaRelative.Computes (δ p) X p) :
    ∃ Q : AlphaTerm, Q.Closed ∧ ∀ p m, OracleRuns (δ p) Q 0 m ↔ m = 1 ∧ p ∈ U := by
  obtain ⟨W, ⟨P, hP, hW⟩, rfl⟩ := hU
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  let T := openTrialProgram e E X
  have ht (p) := openTrialProgram_computes (hE p) (hX p) e
  refine ⟨relativeSearchProgram T, relativeSearchProgram_closed (ht (fun _ => 0)).1, fun p m => ?_⟩
  rw [relativeSearchProgram_runs_iff (ht p)]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨k, hk⟩
    have hac : acceptanceTest ε e
        (Nat.pair (NatListCode.encode (seqPrefix p k.unpair.1)) k.unpair.2) = true := by
      by_contra hn
      simp only [Nat.unpair_pair, hn, ite_false, ne_eq, not_true_eq_false] at hk
    have hr := (oracle_outputTest_exists_iff ε e (NatListCode.encode (seqPrefix p k.unpair.1)) 1).mp
      ⟨k.unpair.2, by simpa only [acceptanceTest, Term.oracleOutputCandidate, Nat.unpair_pair] using hac⟩
    rw [he] at hr
    exact mem_cylinderCode.mpr ⟨seqPrefix p k.unpair.1, (hW _).mpr hr,
      prefixOfSeq_seqPrefix p _⟩
  · intro hp
    obtain ⟨s, hs, hsp⟩ := mem_cylinderCode.mp hp
    have hr := (hW s).mp hs
    rw [← he] at hr
    obtain ⟨b, hb⟩ := (oracle_outputTest_exists_iff ε e (NatListCode.encode s) 1).mpr hr
    refine ⟨Nat.pair s.length b, ?_⟩
    have hs' := seqPrefix_eq_of_mem_cyl hsp
    simp only [Nat.unpair_pair, hs', acceptanceTest, Nat.unpair_pair, hb, ite_true, ne_eq, one_ne_zero, not_false_eq_true]

/-- Paired input for the relative statement; the unpaired mode also gives
the ordinary name-semidecision statement without a reflection assumption. -/
def openInputName (joined : Bool) (ε p : ℕ → ℕ) (n : ℕ) : ℕ :=
  if joined then Nat.pair (ε n) (p n) else p n

def zeroExtendedWord (s : List ℕ) (n : ℕ) : ℕ := s.getD n 0

def wordDigitProgram : AlphaTerm := numericalCompose listGetTerm
  (pairNumerical (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
    (numericalProjectionTerm false))

theorem wordDigitProgram_computes : NumericalComputes wordDigitProgram
    (fun z => zeroExtendedWord (NatListCode.decode z.unpair.1.unpair.1) z.unpair.2) := by
  simpa only [wordDigitProgram, zeroExtendedWord, Nat.unpair_pair, ite_true, Bool.false_eq_true, ite_false] using
    listGet_computes.comp (((projection_computes true).comp (projection_computes true)).pair
      (projection_computes false))

def wordInputAccessProgram (joined : Bool) : AlphaTerm :=
  if joined then pairOutputProgram
    (queryOutputProgram (liftNumericalProgram (numericalProjectionTerm false)))
    (liftNumericalProgram wordDigitProgram)
  else liftNumericalProgram wordDigitProgram

theorem wordInputAccessProgram_computes (joined : Bool) :
    UniformNumericalComputes (wordInputAccessProgram joined)
      (fun ε z => openInputName joined ε (zeroExtendedWord (NatListCode.decode z.unpair.1.unpair.1)) z.unpair.2) := by
  cases joined
  · exact wordDigitProgram_computes.uniform
  · simpa only [wordInputAccessProgram, openInputName, ite_true, Bool.false_eq_true, ite_false] using
      (projection_computes false).uniform.query.pair wordDigitProgram_computes.uniform

def wordCandidateProgram (joined : Bool) (e : ℕ) : AlphaTerm :=
  dataInputProgram
    (reindexProgram (candidateTestProgram e)
      (pairNumerical (numericalConstant 0) (numericalProjectionTerm false)))
    (wordInputAccessProgram joined)

theorem wordCandidateProgram_computes (joined : Bool) (e : ℕ) :
    UniformNumericalComputes (wordCandidateProgram joined e)
      (fun ε z => if Term.oracleOutputCandidate
        (openInputName joined ε (zeroExtendedWord (NatListCode.decode z.unpair.1))) e 0 z.unpair.2 then 1 else 0) := by
  simpa only [wordCandidateProgram, candidateTest, Nat.unpair_pair, Bool.false_eq_true, ite_false, ite_true] using
    (((candidateTestProgram_computes e).reindex
      ((numericalConstant_computes 0).pair (projection_computes false))).dataInput
      (wordInputAccessProgram_computes joined))

def wordStageGuardProgram : AlphaTerm := numericalIfLe
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
  (numericalCompose listLengthTerm (numericalProjectionTerm true))
  (numericalConstant 1) (numericalConstant 0)

theorem wordStageGuardProgram_computes : NumericalComputes wordStageGuardProgram
    (fun z => if z.unpair.2.unpair.2 ≤ (NatListCode.decode z.unpair.1).length then 1 else 0) := by
  simpa only [wordStageGuardProgram, Nat.unpair_pair, Bool.false_eq_true, ite_false, ite_true] using
    (((projection_computes false).comp (projection_computes false)).ifLe
      (listLength_computes.comp (projection_computes true))
      (numericalConstant_computes 1) (numericalConstant_computes 0))

def wordTrialProgram (joined : Bool) (e : ℕ) : AlphaTerm :=
  mapOutputProgram (mulNumerical (numericalProjectionTerm true) (numericalProjectionTerm false))
    (pairOutputProgram (wordCandidateProgram joined e) (liftNumericalProgram wordStageGuardProgram))

theorem wordTrialProgram_computes (joined : Bool) (e : ℕ) (ε : ℕ → ℕ) :
    LambdaRelative.Computes ε (wordTrialProgram joined e)
      (fun z : ℕ => (if Term.oracleOutputCandidate
        (openInputName joined ε (zeroExtendedWord (NatListCode.decode z.unpair.1))) e 0 z.unpair.2 then 1 else 0) *
        (if z.unpair.2.unpair.2 ≤ (NatListCode.decode z.unpair.1).length then 1 else 0)) := by
  have hc : LambdaRelative.Computes ε (wordCandidateProgram joined e)
      (fun z : ℕ => if Term.oracleOutputCandidate
        (openInputName joined ε (zeroExtendedWord (NatListCode.decode z.unpair.1))) e 0 z.unpair.2 then 1 else 0) :=
    ⟨(wordCandidateProgram_computes joined e).1, (wordCandidateProgram_computes joined e).2 ε⟩
  simpa only [wordTrialProgram, Nat.unpair_pair, Bool.false_eq_true, ite_false, ite_true] using
    (hc.pair (LambdaRelative.ofNumerical wordStageGuardProgram_computes ε)).map
      ((projection_computes true).mul (projection_computes false))

def acceptedOpenWords (joined : Bool) (ε : ℕ → ℕ) (e : ℕ) : Set (List ℕ) :=
  {s | ∃ k : ℕ, k.unpair.2 ≤ s.length ∧
    Term.oracleOutputCandidate (openInputName joined ε (zeroExtendedWord s)) e 0 k = true}

theorem acceptedOpenWords_semidecidable (joined : Bool) (ε : ℕ → ℕ) (e : ℕ) :
    LambdaRelative.SemidecidablePredicate ε (· ∈ acceptedOpenWords joined ε e) := by
  have ht := wordTrialProgram_computes joined e ε
  refine ⟨relativeSearchProgram (wordTrialProgram joined e), relativeSearchProgram_closed ht.1, fun s => ?_⟩
  rw [relativeSearchProgram_runs_iff ht]
  simp only [true_and, show Encodable.encode s = NatListCode.encode s from rfl,
    Nat.unpair_pair, NatListCode.decode_encode]
  apply exists_congr
  intro k
  by_cases hc : Term.oracleOutputCandidate (openInputName joined ε (zeroExtendedWord s)) e 0 k = true <;>
    by_cases hb : k.unpair.2 ≤ s.length <;> simp [hc, hb]

theorem zeroExtendedWord_agrees {p : ℕ → ℕ} {s : List ℕ} (hs : prefixOfSeq s p)
    (i : ℕ) (hi : i < s.length) : zeroExtendedWord s i = p i := by
  simpa only [zeroExtendedWord, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, List.get_eq_getElem] using (hs i hi).symm

theorem openInputName_agrees (joined : Bool) (ε p q : ℕ → ℕ) (n : ℕ)
    (h : ∀ i < n, p i = q i) :
    ∀ i < n, openInputName joined ε p i = openInputName joined ε q i := by
  intro i hi
  cases joined <;> simp only [openInputName, ite_true, Bool.false_eq_true, ite_false, h i hi]

/-- Finite certificate bounds produce a whole accepted cylinder, and every
actual output produces such a prefix. This includes arbitrary numeral outputs. -/
theorem semidecision_implies_enumerated_open (joined : Bool) (ε : ℕ → ℕ) (U : Set (ℕ → ℕ))
    (P : AlphaTerm) (hP : P.Closed)
    (hU : ∀ p, (∃ m, OracleRuns (openInputName joined ε p) P 0 m) ↔ p ∈ U) :
    RelativelyEffectivelyOpen ε U := by
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  refine ⟨acceptedOpenWords joined ε e, acceptedOpenWords_semidecidable joined ε e, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := (hU p).mpr hp
    rw [← he] at hm
    obtain ⟨b, hb⟩ := (oracle_outputTest_exists_iff (openInputName joined ε p) e 0 m).mpr hm
    refine mem_cylinderCode.mpr ⟨seqPrefix p b, ⟨Nat.pair m b, by simp, ?_⟩,
      prefixOfSeq_seqPrefix p b⟩
    have ha := openInputName_agrees joined ε (zeroExtendedWord (seqPrefix p b)) p b
      (fun i hi => zeroExtendedWord_agrees (prefixOfSeq_seqPrefix p b) i (by simpa using hi))
    simpa only [Term.oracleOutputCandidate, Nat.unpair_pair] using
      (Term.boundedInputTest_eq_of_stage_prefix _ _ b ha).trans hb
  · intro hp
    obtain ⟨s, ⟨k, hlen, hk⟩, hsp⟩ := mem_cylinderCode.mp hp
    have ha := openInputName_agrees joined ε p (zeroExtendedWord s) k.unpair.2
      (fun i hi => (zeroExtendedWord_agrees hsp i (hi.trans_le hlen)).symm)
    have hc : Term.oracleOutputCandidate (openInputName joined ε p) e 0 k = true :=
      (Term.boundedInputTest_eq_of_stage_prefix _ _ k.unpair.2 ha).trans hk
    have hr := (oracle_outputTest_exists_iff (openInputName joined ε p) e 0 k.unpair.1).mp ⟨k.unpair.2, hc⟩
    rw [he] at hr
    exact (hU p).mp ⟨_, hr⟩

/-- A fixed original parameter and the varying point are supplied together;
one closed term semidecides all members, retaining that same parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus membership in a $\lSigma^0_1$ set is semidecidable: given $p \in \BaireSpace$, search the enumeration of cylinders
    until one appears whose finite word is an initial segment of $p$. If $p \in U$, the search eventually halts; if $p
    \notin U$, it may run forever. Dually, membership in a $\lPi^0_1$ set is co-semidecidable.
-/
theorem relativelyEffectivelyOpen_iff_name_semidecidable (ε : ℕ → ℕ) (U : Set (ℕ → ℕ)) :
    RelativelyEffectivelyOpen ε U ↔ ∃ P : AlphaTerm, P.Closed ∧
      ∀ p, (∃ m, OracleRuns (LambdaTree.sectionParameter ε p) P 0 m) ↔ p ∈ U := by
  constructor
  · intro hU
    obtain ⟨P, hP, h⟩ := effectivelyOpen_semidecision_with_accessors hU (LambdaTree.sectionParameter ε)
      (LambdaTree.parameterProjectionProgram true) (LambdaTree.parameterProjectionProgram false)
      (fun p => LambdaTree.parameterProjection_computes true ε p)
      (fun p => LambdaTree.parameterProjection_computes false ε p)
    exact ⟨P, hP, fun p => by simp only [h p, exists_eq_left]⟩
  · rintro ⟨P, hP, h⟩
    exact semidecision_implies_enumerated_open true ε U P hP h

/-- The enumerated-cylinder definition and the named lightface definition
give the same effectively open subsets of Baire space. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus membership in a $\lSigma^0_1$ set is semidecidable: given $p \in \BaireSpace$, search the enumeration of cylinders
    until one appears whose finite word is an initial segment of $p$. If $p \in U$, the search eventually halts; if $p
    \notin U$, it may run forever. Dually, membership in a $\lPi^0_1$ set is co-semidecidable.
-/
theorem effectivelyOpen_iff_lambdaSigma01 (U : Set (ℕ → ℕ)) :
    EffectivelyOpen U ↔ LambdaSigma01 U := by
  constructor
  · intro hU
    obtain ⟨P, hP, h⟩ := effectivelyOpen_semidecision_with_accessors hU id
      (constantProgram 0) identityProgram
      (fun p => ⟨constantProgram_closed 0, constantProgram_runs 0 p⟩)
      (fun p => ⟨identityProgram_closed, identityProgram_runs p⟩)
    exact ⟨P, hP, fun p => by
      change (∃ m, OracleRuns p.val P 0 m) ↔ p.val ∈ U
      constructor
      · rintro ⟨m, hm⟩
        exact ((h p.val m).mp hm).2
      · intro hp
        exact ⟨1, (h p.val 1).mpr ⟨rfl, hp⟩⟩⟩
  · rintro ⟨P, hP, h⟩
    exact semidecision_implies_enumerated_open false (fun _ => 0) U P hP
      (fun p => h ⟨p, mem_univ p⟩)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus membership in a $\lSigma^0_1$ set is semidecidable: given $p \in \BaireSpace$, search the enumeration of cylinders
    until one appears whose finite word is an initial segment of $p$. If $p \in U$, the search eventually halts; if $p
    \notin U$, it may run forever. Dually, membership in a $\lPi^0_1$ set is co-semidecidable.
-/
theorem effectivelyClosed_iff_complement_lambdaSigma01 (F : Set (ℕ → ℕ)) :
    EffectivelyClosed F ↔ LambdaSigma01 Fᶜ := effectivelyOpen_iff_lambdaSigma01 Fᶜ

end PolishSpaceBook
