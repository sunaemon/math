module

public import PolishSpaceBook.LambdaRecursiveTrees
public import PolishSpaceBook.LambdaRelativeSearch
public import PolishSpaceBook.LambdaOracleOutputSearch

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Total enumerations from lambda acceptance tests

A fixed default member makes failed finite certificate tests harmless.
No decision of emptiness and no termination test for arbitrary programs is used.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
universe u

/-- Acceptance means reaching numeral one; other outputs do not accept. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    For a predicate on coded inputs, call a computation \emph{accepting} when it returns the numeral one.
    A predicate is \emph{semidecidable relative to $\varepsilon$} if a closed program accepts exactly its members.
    Other outputs count as rejection. This gives the same predicates as requiring a program to have a numerical
    output exactly on the members: search the finite computation certificates and return one only after a successful
    test. The two directions, including exclusion of numerical outputs when no test succeeds, are proved in
    §{sec:lambda-total-enumerations}. Thus an effectively open set relative to $\varepsilon$ may be specified by a
    semidecidable family $W$ of finite words and the union $\bigcup_{s\in W}\cyl{s}$. Its complement is effectively closed
    relative to the same parameter.
-/
def Semidecides {α : Type u} [Encodable α] (ε : ℕ → ℕ) (P : AlphaTerm) (R : α → Prop) : Prop :=
  P.Closed ∧ ∀ a, R a ↔ OracleRuns ε P (Encodable.encode a) 1

def SemidecidablePredicate {α : Type u} [Encodable α] (ε : ℕ → ℕ) (R : α → Prop) : Prop :=
  ∃ P, Semidecides ε P R

theorem Decides.semidecides {α : Type u} [Encodable α] {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : α → Prop} (h : Decides ε P R) : Semidecides ε P R := by
  refine ⟨h.1,fun a => ⟨(h.2 a).1,fun hr => ?_⟩⟩
  by_contra hn
  have := hr.output_unique ((h.2 a).2 hn)
  omega

theorem DecidablePredicate.semidecidable {α : Type u} [Encodable α] {ε : ℕ → ℕ}
    {R : α → Prop} (h : DecidablePredicate ε R) : SemidecidablePredicate ε R := by
  obtain ⟨P,hP⟩ := h
  exact ⟨P,hP.semidecides⟩

end LambdaRelative
namespace NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-- On the paired input (n,s), test a paired numerical output and finite certificate bound. -/
def candidateTestProgram (e : ℕ) : AlphaTerm :=
  lam 70 (lam 71 (app (app (app (app oracleOutputCandidateTerm (var 70)) (numeral e))
    (app (numericalProjectionTerm true) (var 71)))
    (app (numericalProjectionTerm false) (var 71))))

theorem candidateTestProgram_closed (e : ℕ) : (candidateTestProgram e).Closed := by
  unfold candidateTestProgram Closed
  simp only [fv_lam,fv_app,fv_var,(show oracleOutputCandidateTerm.fv = ∅ from oracleOutputCandidateTerm_closed),
    (show (numeral e).fv = ∅ from numeral_closed e),
    (show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1),
    (show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1)]
  decide

def candidateTest (ε : ℕ → ℕ) (e z : ℕ) : Bool :=
  Term.oracleOutputCandidate ε e z.unpair.1 z.unpair.2

theorem candidateTestProgram_computes (e : ℕ) :
    UniformNumericalComputes (candidateTestProgram e) (fun ε z => if candidateTest ε e z then 1 else 0) := by
  refine ⟨candidateTestProgram_closed e,fun ε z => ?_⟩
  let B (O Z : AlphaTerm) := app (app (app (app oracleOutputCandidateTerm O) (numeral e))
    (app (numericalProjectionTerm true) Z))
    (app (numericalProjectionTerm false) Z)
  have h₁ : Beta (app (candidateTestProgram e) (var 0)) (lam 71 (B (var 0) (var 71))) := by
    have he : (lam 71 (B (var 70) (var 71))).subst 70 (var 0) =
        lam 71 (B (var 0) (var 71)) := by
      rw [subst_lam_fresh _ _ 71 70 (by decide) (by simp [fv_var])]
      simp only [B,subst_app,subst_var,ite_true,ite_false,show (71 : ℕ) ≠ 70 from by decide,
        subst_closed _ _ _ oracleOutputCandidateTerm_closed,
        subst_closed _ _ _ (numeral_closed e),
        subst_closed _ _ _ (projection_computes true).1,subst_closed _ _ _ (projection_computes false).1]
    change Beta (app (lam 70 (lam 71 (B (var 70) (var 71)))) (var 0)) _
    rw [← he]
    exact Beta.contract 70 _ _
  have h₂ : Beta (app (lam 71 (B (var 0) (var 71))) (numeral z)) (B (var 0) (numeral z)) := by
    convert Beta.contract 71 (B (var 0) (var 71)) (numeral z) using 1
    simp only [B,subst_app,subst_var,ite_true,ite_false,
      show (0 : ℕ) ≠ 71 from by decide,subst_closed _ _ _ oracleOutputCandidateTerm_closed,
      subst_closed _ _ _ (numeral_closed e),
      subst_closed _ _ _ (projection_computes true).1,subst_closed _ _ _ (projection_computes false).1]
  have hr := oracleOutputCandidateTerm_apply ε e z.unpair.1 z.unpair.2
  exact (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
    ((oracle_steps_app (oracle_steps_app_right _ (beta_steps_oracle ((projection_computes true).2 z)))
      (beta_steps_oracle ((projection_computes false).2 z))).trans hr)

/-- Specialize the general candidate to the proposed output one. -/
def acceptanceTestProgram (e : ℕ) : AlphaTerm := reindexProgram (candidateTestProgram e)
  (pairNumerical (numericalProjectionTerm true)
    (pairNumerical (numericalConstant 1) (numericalProjectionTerm false)))

def acceptanceTest (ε : ℕ → ℕ) (e z : ℕ) : Bool :=
  Term.boundedInputTest ε (Term.oracleProgramInput e z.unpair.1) (Term.churchNumeral 1) z.unpair.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Now fix an accepting program index $e$ and a code $a_\ast$ known to be accepted. Write
    $$\begin{aligned}
    a(z)&:=\LambdaNumericProjection{1}z,\qquad r(z):=\LambdaNumericProjection{2}z,\\
    \LambdaAcceptanceTest{e}&:=\lambdaab{o}{\lambdaab{z}{
     \LambdaQueryOutputCandidate\,o\,\ChurchNumeral{e}\,a(z)
     \,\bigl(\LambdaNumericPair\,\ChurchNumeral{1}\,r(z)\bigr)}},\\
    \LambdaTotalEnumeration{e}{a_\ast}&:=\lambdaab{o}{\lambdaab{z}{
     \LambdaLeCase{\ChurchNumeral{1}}{\LambdaAcceptanceTest{e}\,o\,z}{a(z)}{\ChurchNumeral{a_\ast}}}}.
    \end{aligned}$$
    Expand the abbreviations inside the displayed abstractions. The acceptance test returns one exactly when the
    finite bound certifies output one, and returns zero otherwise. Thus the comparison selects the candidate code
    on success and the fixed accepted code on failure. Every component computation terminates.
-/
theorem acceptanceTestProgram_computes (e : ℕ) :
    UniformNumericalComputes (acceptanceTestProgram e) (fun ε z => if acceptanceTest ε e z then 1 else 0) := by
  have h := (candidateTestProgram_computes e).reindex
    ((projection_computes true).pair ((numericalConstant_computes 1).pair (projection_computes false)))
  unfold acceptanceTestProgram
  convert h using 1
  funext ε z
  simp only [candidateTest,acceptanceTest,Term.oracleOutputCandidate,Nat.unpair_pair,Bool.false_eq_true,ite_false,ite_true]

/-- The first component is a zero/one bit and the second is the candidate. -/
def enumerationSelect (a₀ : ℕ) : AlphaTerm := numericalIfLe (numericalConstant 1)
  (numericalProjectionTerm true) (numericalProjectionTerm false) (numericalConstant a₀)

theorem enumerationSelect_computes (a₀ : ℕ) : NumericalComputes (enumerationSelect a₀)
    (fun z => if 1 ≤ z.unpair.1 then z.unpair.2 else a₀) := by
  exact (numericalConstant_computes 1).ifLe (projection_computes true) (projection_computes false)
    (numericalConstant_computes a₀)

def totalEnumerationProgram (e a₀ : ℕ) : AlphaTerm :=
  mapOutputProgram (enumerationSelect a₀)
    (pairOutputProgram (acceptanceTestProgram e) (liftNumericalProgram (numericalProjectionTerm true)))

def totalEnumeration (ε : ℕ → ℕ) (e a₀ z : ℕ) : ℕ :=
  if acceptanceTest ε e z then z.unpair.1 else a₀

theorem totalEnumerationProgram_computes (e a₀ : ℕ) :
    UniformNumericalComputes (totalEnumerationProgram e a₀) (fun ε => totalEnumeration ε e a₀) := by
  have h := ((acceptanceTestProgram_computes e).pair (projection_computes true).uniform).map
    (enumerationSelect_computes a₀)
  unfold totalEnumerationProgram totalEnumeration
  convert h using 1
  funext ε z
  simp only [Nat.unpair_pair]
  split_ifs <;> simp_all

end NamedLambda.AlphaTerm
namespace LambdaRelative

/-- A nonempty accepted set has a total lambda enumeration with exactly its range. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total enumeration by finite acceptance tests
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The candidate checker, projections, pairing, and comparison give totality. A successful test certifies an
    accepting computation, while the default belongs to the accepted set by hypothesis; hence every output belongs
    to that set. If a code is accepted, completeness of the finite checker supplies a bound, and the stage pairing
    that code with the bound returns it. This proves the reverse range inclusion. Decoding the output codes gives
    the word sequence; the two inverse identities of finite-list coding preserve both range inclusions. No code
    validity test is needed because every natural number decodes to exactly one finite word.
-/
theorem SemidecidablePredicate.total_enumeration {ε : ℕ → ℕ} {R : ℕ → Prop}
    (hR : SemidecidablePredicate ε R) (hne : ∃ a, R a) :
    ∃ f : ℕ → ℕ, Computable ε f ∧ ∀ a, R a ↔ a ∈ Set.range f := by
  obtain ⟨a₀,ha₀⟩ := hne
  obtain ⟨P,hP⟩ := hR
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP.1
  have hspec (n : ℕ) : R n ↔ ∃ s, acceptanceTest ε e (Nat.pair n s) = true := by
    rw [hP.2 n]
    simp only [acceptanceTest,Nat.unpair_pair,Encodable.encode_nat]
    rw [oracle_outputTest_exists_iff,he]
  refine ⟨totalEnumeration ε e a₀,⟨totalEnumerationProgram e a₀,
    (totalEnumerationProgram_computes e a₀).1,(totalEnumerationProgram_computes e a₀).2 ε⟩,fun a => ⟨?_,?_⟩⟩
  · intro ha
    obtain ⟨s,hs⟩ := (hspec a).mp ha
    exact ⟨Nat.pair a s,by simp [totalEnumeration,hs]⟩
  · rintro ⟨z,rfl⟩
    unfold totalEnumeration
    split_ifs with h
    · exact (hspec _).mpr ⟨z.unpair.2,by simpa only [Nat.pair_unpair] using h⟩
    · exact ha₀

/-- Arbitrary numerical output is witnessed by a candidate output and a finite bound. -/
theorem candidateTest_exists_iff (ε : ℕ → ℕ) (e n : ℕ) :
    (∃ k, candidateTest ε e (Nat.pair n k) = true) ↔
      ∃ m, OracleRuns ε (Term.closedProgram e) n m := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k.unpair.1,(oracle_outputTest_exists_iff ε e n _).mp ⟨k.unpair.2,?_⟩⟩
    simpa only [candidateTest,Nat.unpair_pair,Term.oracleOutputCandidate] using hk
  · rintro ⟨m,hm⟩
    obtain ⟨r,hr⟩ := (oracle_outputTest_exists_iff ε e n m).mpr hm
    exact ⟨Nat.pair m r,by simpa only [candidateTest,Term.oracleOutputCandidate,Nat.unpair_pair] using hr⟩

/-- Acceptance and exact numerical halting domains define the same predicates. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Acceptance and numerical halting domains
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Given an accepting program with index $e$, use the total candidate checker of §{sec:lambda-input-universal-evaluation}
    to search bounds for a computation with output one. Conversely, for a program with a prescribed numerical halting
    domain, search pairs consisting of a proposed output numeral and a certificate bound. Each candidate test is
    total. Its soundness and completeness say that some test succeeds exactly when the specified output, or some
    numerical output, respectively, exists. Apply the exact relative search lemma, which returns one on success and
    has no numerical output otherwise. This proves both implications without deciding nontermination.
-/
theorem semidecidable_iff_domain {α : Type u} [Encodable α] (ε : ℕ → ℕ) (R : α → Prop) :
    SemidecidablePredicate ε R ↔
      ∃ P : AlphaTerm, P.Closed ∧ ∀ a, R a ↔ ∃ m, OracleRuns ε P (Encodable.encode a) m := by
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP.1
    have ht : Computes ε (acceptanceTestProgram e) (fun z => if acceptanceTest ε e z then 1 else 0) :=
      ⟨(acceptanceTestProgram_computes e).1,(acceptanceTestProgram_computes e).2 ε⟩
    refine ⟨relativeSearchProgram (acceptanceTestProgram e),relativeSearchProgram_closed ht.1,fun a => ?_⟩
    have ha : R a ↔ ∃ k, acceptanceTest ε e (Nat.pair (Encodable.encode a) k) = true := by
      rw [hP.2 a]
      simp only [acceptanceTest,Nat.unpair_pair]
      rw [oracle_outputTest_exists_iff,he]
    simp only [relativeSearchProgram_runs_iff ht]
    simpa using ha
  · rintro ⟨P,hP,hR⟩
    obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
    have ht : Computes ε (candidateTestProgram e) (fun z => if candidateTest ε e z then 1 else 0) :=
      ⟨(candidateTestProgram_computes e).1,(candidateTestProgram_computes e).2 ε⟩
    refine ⟨relativeSearchProgram (candidateTestProgram e),relativeSearchProgram_closed ht.1,fun a => ?_⟩
    rw [relativeSearchProgram_runs_iff ht]
    have ha := candidateTest_exists_iff ε e (Encodable.encode a)
    rw [he,← hR a] at ha
    simpa using ha.symm

end LambdaRelative
namespace LambdaTree
local instance : Encodable (List ℕ) := NatListCode.encodable

/-- The book's bijective list code converts numerical enumeration back to words. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Total enumeration of a nonempty semidecidable family
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Choose $s_\ast\in W$ and an index for its accepting program. Decode the stage as a pair $(a,r)$, where $a$ is a
    word code and $r$ bounds a finite search for a computation returning one on that code. Run the total certificate
    test with parameter $\varepsilon$. If it succeeds, output the word coded by $a$; otherwise output $s_\ast$.
    The explicit lambda programs for the test and selection are given in §{sec:lambda-total-enumerations}.
    Each stage terminates even when the original accepting computation does not. Soundness of the certificate test
    ensures that every output belongs to $W$. Conversely, every word in $W$ has a finite accepting computation,
    so some bound certifies it and a stage with that word code outputs it. This proves equality of the range.
    The chosen member is fixed data in the program; this argument does not decide whether a given family is empty.
-/
theorem total_word_enumeration {ε : ℕ → ℕ} {W : Set (List ℕ)}
    (hW : LambdaRelative.SemidecidablePredicate ε (· ∈ W)) (hne : W.Nonempty) :
    ∃ (f : ℕ → List ℕ) (P : AlphaTerm),
      LambdaRelative.Computes ε P (fun n => NatListCode.encode (f n)) ∧
      ∀ s, s ∈ W ↔ s ∈ Set.range f := by
  obtain ⟨P,hP⟩ := hW
  have hR : LambdaRelative.SemidecidablePredicate ε (fun n : ℕ => NatListCode.decode n ∈ W) := by
    refine ⟨P,hP.1,fun n => ?_⟩
    have h := hP.2 (NatListCode.decode n)
    change NatListCode.decode n ∈ W ↔ OracleRuns ε P (NatListCode.encode (NatListCode.decode n)) 1 at h
    simpa only [NatListCode.encode_decode,Encodable.encode_nat] using h
  obtain ⟨a,ha⟩ := hne
  obtain ⟨f,⟨Q,hQ⟩,hr⟩ := hR.total_enumeration ⟨NatListCode.encode a,by simpa using ha⟩
  refine ⟨fun n => NatListCode.decode (f n),Q,?_,fun s => ?_⟩
  · simpa only [NatListCode.encode_decode] using hQ
  · constructor
    · intro hs
      obtain ⟨n,hn⟩ := (hr (NatListCode.encode s)).mp (by simpa using hs)
      exact ⟨n,by simp [hn]⟩
    · rintro ⟨n,rfl⟩
      exact (hr (f n)).mpr ⟨n,rfl⟩

end LambdaTree
end PolishSpaceBook
