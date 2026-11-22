module

public import PolishSpaceBook.LambdaOpenSemidecision

@[expose] public section

/-! # Effective changes of the finite-word enumeration

All code translations below are backed by total lambda computations. A word
listing may repeat entries; its range need not have a decidable inverse.
-/
noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
local instance effectiveOpenCodingWords : Encodable (List ℕ) := NatListCode.encodable

namespace LambdaRelative

/-- A total input translator is applied inside the finite acceptance test,
so no converse theorem for arbitrary partial composition is assumed. -/
theorem SemidecidablePredicate.precompNumerical {ε : ℕ → ℕ} {R : ℕ → Prop}
    {g : ℕ → ℕ} {G : AlphaTerm} (hR : SemidecidablePredicate ε R)
    (hG : Computes ε G g) : SemidecidablePredicate ε (fun n => R (g n)) := by
  obtain ⟨P, hP, hR⟩ := hR
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  have ha : Computes ε (acceptanceTestProgram e)
      (fun z : ℕ => if acceptanceTest ε e z then 1 else 0) :=
    ⟨(acceptanceTestProgram_computes e).1, (acceptanceTestProgram_computes e).2 ε⟩
  have ht := ha.comp ((hG.reindex (projection_computes true)).pair
    (ofNumerical (projection_computes false) ε))
  refine ⟨relativeSearchProgram _, relativeSearchProgram_closed ht.1, fun n => ?_⟩
  rw [relativeSearchProgram_runs_iff ht]
  simp only [Nat.unpair_pair, true_and]
  have hh : R (g n) ↔ ∃ k, acceptanceTest ε e (Nat.pair (g n) k) = true := by
    rw [hR, ← he]
    simpa only [acceptanceTest, Term.oracleOutputCandidate, Nat.unpair_pair, Encodable.encode_nat] using
      (oracle_outputTest_exists_iff ε e (g n) 1).symm
  simpa using hh

/-- Equality of two numeral coordinates is computed by the lambda equality term. -/
def codeEqualityProgram : AlphaTerm := numericalCombine equalityTerm
  (numericalProjectionTerm true) (numericalProjectionTerm false)

theorem codeEqualityProgram_computes : NumericalComputes codeEqualityProgram
    (fun z => if z.unpair.1 = z.unpair.2 then 1 else 0) := by
  simpa only [codeEqualityProgram, ite_true, Bool.false_eq_true, ite_false] using
    (projection_computes true).combine (projection_computes false) equalityTerm_closed
      (fun a b => if a = b then 1 else 0) equalityTerm_apply

/-- Search simultaneously for a preimage and its finite acceptance certificate.
No injectivity or effective inverse of the translator is required. -/
theorem SemidecidablePredicate.imageNumerical {ε : ℕ → ℕ} {R : ℕ → Prop}
    {g : ℕ → ℕ} {G : AlphaTerm} (hR : SemidecidablePredicate ε R)
    (hG : Computes ε G g) : SemidecidablePredicate ε (fun y => ∃ n, R n ∧ g n = y) := by
  obtain ⟨P, hP, hR⟩ := hR
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  have ha : Computes ε (acceptanceTestProgram e)
      (fun z : ℕ => if acceptanceTest ε e z then 1 else 0) :=
    ⟨(acceptanceTestProgram_computes e).1, (acceptanceTestProgram_computes e).2 ε⟩
  have hc := ha.reindex (projection_computes false)
  have hg := hG.reindex ((projection_computes true).comp (projection_computes false))
  have hq := (hg.pair (ofNumerical (projection_computes true) ε)).map codeEqualityProgram_computes
  have ht := (hc.pair hq).map ((projection_computes true).mul (projection_computes false))
  refine ⟨relativeSearchProgram _, relativeSearchProgram_closed ht.1, fun y => ?_⟩
  rw [relativeSearchProgram_runs_iff ht]
  simp only [Nat.unpair_pair, Bool.false_eq_true, ite_false, ite_true, true_and]
  have hh (n) : R n ↔ ∃ b, acceptanceTest ε e (Nat.pair n b) = true := by
    rw [hR, ← he]
    simpa only [acceptanceTest, Term.oracleOutputCandidate, Nat.unpair_pair, Encodable.encode_nat] using
      (oracle_outputTest_exists_iff ε e n 1).symm
  constructor
  · rintro ⟨n, hn, hny⟩
    obtain ⟨b, hb⟩ := (hh n).mp hn
    exact ⟨Nat.pair n b, by simp [Nat.unpair_pair, hb, hny]⟩
  · rintro ⟨k, hk⟩
    have hc : acceptanceTest ε e k = true := by
      by_contra h
      simp [h] at hk
    have hg : g k.unpair.1 = y := by
      by_contra h
      simp [h] at hk
    refine ⟨k.unpair.1, (hh _).mpr ⟨k.unpair.2, ?_⟩, hg⟩
    simpa only [Nat.pair_unpair] using hc

end LambdaRelative

/-- The canonical word encoding is bijective and therefore introduces no
extra restriction on acceptance predicates. -/
theorem word_semidecidable_iff_code (ε : ℕ → ℕ) (W : Set (List ℕ)) :
    LambdaRelative.SemidecidablePredicate ε (· ∈ W) ↔
      LambdaRelative.SemidecidablePredicate ε (fun n : ℕ => NatListCode.decode n ∈ W) := by
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, fun n => ?_⟩
    simpa only [show Encodable.encode (NatListCode.decode n) =
      NatListCode.encode (NatListCode.decode n) from rfl, NatListCode.encode_decode,
      Encodable.encode_nat] using h (NatListCode.decode n)
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    intro s
    change s ∈ W ↔ OracleRuns ε P (NatListCode.encode s) 1
    simpa only [NatListCode.decode_encode, Encodable.encode_nat] using h (NatListCode.encode s)

/-- A numerical listing of words with a semidecidable set of selected indices. -/
def openFromWordListing (ε : ℕ → ℕ) (σ : ℕ → List ℕ) (U : Set (ℕ → ℕ)) : Prop :=
  ∃ W : Set ℕ, LambdaRelative.SemidecidablePredicate ε (· ∈ W) ∧
    U = {p | ∃ n ∈ W, prefixOfSeq (σ n) p}

/-- Any computable surjective listing of finite words defines the same
pointclass. Duplicated words cause no problem: the reverse direction uses
computable images rather than choosing an inverse. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The enumeration $\IndexedFamily{W_e}{e\in\omega}$ is bookkeeping, not extra structure in the pointclass. It supplies
    indices for
    recursively enumerable sets, so that effectively open sets can be coded. If one replaces it by another standard
    effective enumeration, the indices change but the class $\lSigma^0_1$ does not: the same recursively enumerable subsets
    of $\omega$ are being listed. The same applies to the fixed coding $\sigma:\omega\to\finseq{\omega}$ of finite
    sequences. These choices affect codes, not the underlying lightface classes.
-/
theorem openFromWordListing_iff {ε : ℕ → ℕ} (σ : ℕ → List ℕ)
    (hσ : Function.Surjective σ) {S : AlphaTerm}
    (hS : NumericalComputes S (fun n => NatListCode.encode (σ n))) (U : Set (ℕ → ℕ)) :
    openFromWordListing ε σ U ↔ RelativelyEffectivelyOpen ε U := by
  constructor
  · rintro ⟨W, hW, rfl⟩
    let V : Set (List ℕ) := σ '' W
    have hi := hW.imageNumerical (LambdaRelative.ofNumerical hS ε)
    have hv : LambdaRelative.SemidecidablePredicate ε (fun n : ℕ => NatListCode.decode n ∈ V) := by
      convert hi using 1
      funext n
      apply propext
      simp only [V, Set.mem_image]
      constructor
      · rintro ⟨a, ha, he⟩
        exact ⟨a, ha, by rw [he, NatListCode.encode_decode]⟩
      · rintro ⟨a, ha, he⟩
        exact ⟨a, ha, by rw [← he, NatListCode.decode_encode]⟩
    refine ⟨V, (word_semidecidable_iff_code ε V).mpr hv, ?_⟩
    ext p
    simp only [Set.mem_ofPred_eq, mem_cylinderCode, V, Set.mem_image]
    constructor
    · rintro ⟨n, hn, hp⟩
      exact ⟨σ n, ⟨n, hn, rfl⟩, hp⟩
    · rintro ⟨s, ⟨n, hn, rfl⟩, hp⟩
      exact ⟨n, hn, hp⟩
  · rintro ⟨V, hV, rfl⟩
    have hw := ((word_semidecidable_iff_code ε V).mp hV).precompNumerical
      (LambdaRelative.ofNumerical hS ε)
    simp only [NatListCode.decode_encode] at hw
    refine ⟨{n | σ n ∈ V}, hw, ?_⟩
    ext p
    simp only [mem_cylinderCode, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨s, hs, hp⟩
      obtain ⟨n, rfl⟩ := hσ s
      exact ⟨n, hs, hp⟩
    · rintro ⟨n, hn, hp⟩
      exact ⟨σ n, hn, hp⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The enumeration $\IndexedFamily{W_e}{e\in\omega}$ is bookkeeping, not extra structure in the pointclass. It supplies
    indices for
    recursively enumerable sets, so that effectively open sets can be coded. If one replaces it by another standard
    effective enumeration, the indices change but the class $\lSigma^0_1$ does not: the same recursively enumerable subsets
    of $\omega$ are being listed. The same applies to the fixed coding $\sigma:\omega\to\finseq{\omega}$ of finite
    sequences. These choices affect codes, not the underlying lightface classes.
-/
theorem openFromWordListing_invariance {ε : ℕ → ℕ} (σ τ : ℕ → List ℕ)
    (hσ : Function.Surjective σ) (hτ : Function.Surjective τ) {S T : AlphaTerm}
    (hS : NumericalComputes S (fun n => NatListCode.encode (σ n)))
    (hT : NumericalComputes T (fun n => NatListCode.encode (τ n))) (U : Set (ℕ → ℕ)) :
    openFromWordListing ε σ U ↔ openFromWordListing ε τ U :=
  (openFromWordListing_iff σ hσ hS U).trans (openFromWordListing_iff τ hτ hT U).symm

/-- A different index family listing the same subsets changes only indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The enumeration $\IndexedFamily{W_e}{e\in\omega}$ is bookkeeping, not extra structure in the pointclass. It supplies
    indices for
    recursively enumerable sets, so that effectively open sets can be coded. If one replaces it by another standard
    effective enumeration, the indices change but the class $\lSigma^0_1$ does not: the same recursively enumerable subsets
    of $\omega$ are being listed. The same applies to the fixed coding $\sigma:\omega\to\finseq{\omega}$ of finite
    sequences. These choices affect codes, not the underlying lightface classes.
-/
theorem wordIndexFamily_invariance (F G : ℕ → Set ℕ) (h : Set.range F = Set.range G)
    (σ : ℕ → List ℕ) (U : Set (ℕ → ℕ)) :
    (∃ e, U = {p | ∃ n ∈ F e, prefixOfSeq (σ n) p}) ↔
      ∃ e, U = {p | ∃ n ∈ G e, prefixOfSeq (σ n) p} := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨d, hd⟩ := h ▸ Set.mem_range_self e
    exact ⟨d, hd ▸ he⟩
  · rintro ⟨e, he⟩
    obtain ⟨d, hd⟩ := h.symm ▸ Set.mem_range_self e
    exact ⟨d, hd ▸ he⟩

end PolishSpaceBook
