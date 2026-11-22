module

public import PolishSpaceBook.EffectiveClosedTreeRepresentation
public import PolishSpaceBook.LambdaUniformInterpreter
public import PolishSpaceBook.LambdaIndexedTrees
public import PolishSpaceBook.LambdaListPrefixes
public import PolishSpaceBook.EffectiveDSTLightfaceHierarchies

@[expose] public section

/-! # Natural-number universal families of effectively open sets

The parameter is a lambda syntax index. The fixed recursive enumeration of
finite words is the book's natural-number list decoding. Acceptance means
output one, exactly as in the chapter's definition of semidecidability.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm

local instance universalOpenWordEncoding : Encodable (List ℕ) := NatListCode.encodable

/-- Explicit product coding keeps the numerical index and the word code separate. -/
@[reducible] def universalOpenPairEncoding : Encodable (ℕ × List ℕ) where
  encode z := Nat.pair z.1 (NatListCode.encode z.2)
  decode n := some (n.unpair.1, NatListCode.decode n.unpair.2)
  encodek z := by simp
local instance universalOpenPairEncodable : Encodable (ℕ × List ℕ) := universalOpenPairEncoding

/-- Effectively open subsets of the discrete naturals times Baire space are
unions of a semidecidable family of product cylinders. -/
def RelativelyEffectivelyOpenNatBaire (ε : ℕ → ℕ) (U : Set (ℕ × (ℕ → ℕ))) : Prop :=
  ∃ W : Set (ℕ × List ℕ), LambdaRelative.SemidecidablePredicate ε (· ∈ W) ∧
    ∀ e p, (e, p) ∈ U ↔ ∃ s, (e, s) ∈ W ∧ prefixOfSeq s p

/-- Word decoding is recursive in the book's encoding: its output code is the
input numeral itself, so the lambda program ignores the oracle. -/
theorem universalOpen_wordEnumeration (ε : ℕ → ℕ) :
    LambdaRelative.Computable ε NatListCode.decode := by
  let I : AlphaTerm := lam 1 (lam 2 (var 2))
  refine ⟨I, ?_, ?_⟩
  · unfold I Closed
    simp only [fv_lam, fv_var]
    decide
  · intro n
    change OracleRuns ε I n (NatListCode.encode (NatListCode.decode n))
    rw [NatListCode.encode_decode]
    have h1 : Beta (app I (var 0)) (lam 2 (var 2)) := by
      convert Beta.contract 1 (lam 2 (var 2)) (var 0) using 1
      simp [subst_lam_fresh, fv_var, subst_var]
    have h2 : Beta (app (lam 2 (var 2)) (numeral n)) (numeral n) := by
      simpa only [subst_var, ite_true] using Beta.contract 2 (var 2) (numeral n)
    exact beta_steps_oracle (.tail (.single (.app_left _ h1)) h2)

/-- The e-th recursively enumerable word family, with the fixed input parameter retained. -/
def universalOpenWords (ε : ℕ → ℕ) (e : ℕ) : Set (List ℕ) :=
  {s | OracleRuns ε (Term.closedProgram e) (NatListCode.encode s) 1}

/-- The product-cylinder union from the book. -/
def effectiveOpenUniversal (ε : ℕ → ℕ) : Set (ℕ × (ℕ → ℕ)) :=
  {z | z.2 ∈ cylinderCode (universalOpenWords ε z.1)}

/-- A single lambda evaluator semidecides the whole family of indexed words. -/
theorem universalOpenWords_uniform (ε : ℕ → ℕ) :
    LambdaRelative.SemidecidablePredicate ε
      (fun z : ℕ × List ℕ => z.2 ∈ universalOpenWords ε z.1) := by
  refine ⟨uniformInterpreterProgram, uniformInterpreterProgram_closed, ?_⟩
  rintro ⟨e, s⟩
  exact (uniformInterpreterProgram_runs_iff ε e (NatListCode.encode s) 1).symm

/-- Each section is effectively open relative to the very same parameter. -/
theorem effectiveOpenUniversal_section (ε : ℕ → ℕ) (e : ℕ) :
    RelativelyEffectivelyOpen ε {p | (e, p) ∈ effectiveOpenUniversal ε} := by
  refine ⟨universalOpenWords ε e, ?_, rfl⟩
  exact ⟨Term.closedProgram e, Term.closedProgram_closed e, fun _ => Iff.rfl⟩

/-- The uniform semidecider gives effective openness in the product presentation. -/
theorem effectiveOpenUniversal_effectivelyOpen (ε : ℕ → ℕ) :
    RelativelyEffectivelyOpenNatBaire ε (effectiveOpenUniversal ε) := by
  refine ⟨{z | z.2 ∈ universalOpenWords ε z.1}, universalOpenWords_uniform ε, ?_⟩
  intro e p
  exact mem_cylinderCode

/-- Every effectively open set occurs as a natural-number section. -/
theorem effectiveOpenUniversal_universal (ε : ℕ → ℕ) (U : Set (ℕ → ℕ))
    (hU : RelativelyEffectivelyOpen ε U) :
    ∃ e, U = {p | (e, p) ∈ effectiveOpenUniversal ε} := by
  obtain ⟨W, ⟨A, hA, hW⟩, rfl⟩ := hU
  obtain ⟨e, he⟩ := Term.closedProgram_surjective A hA
  refine ⟨e, ?_⟩
  have hwords : W = universalOpenWords ε e := by
    ext s
    change s ∈ W ↔ OracleRuns ε (Term.closedProgram e) (NatListCode.encode s) 1
    rw [he]
    exact hW s
  rw [hwords]
  rfl

/-- Express the same union with the book's fixed recursive word enumeration. -/
theorem effectiveOpenUniversal_union (ε : ℕ → ℕ) (e : ℕ) (p : ℕ → ℕ) :
    (e, p) ∈ effectiveOpenUniversal ε ↔
      ∃ n, OracleRuns ε (Term.closedProgram e) n 1 ∧ prefixOfSeq (NatListCode.decode n) p := by
  change p ∈ cylinderCode (universalOpenWords ε e) ↔ _
  rw [mem_cylinderCode]
  constructor
  · rintro ⟨s, hs, hsp⟩
    exact ⟨NatListCode.encode s, hs, by simpa using hsp⟩
  · rintro ⟨n, hn, hnp⟩
    refine ⟨NatListCode.decode n, ?_, hnp⟩
    simpa [universalOpenWords] using hn

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  excerpt: |
    \begin{theorem*}[$\lSigma^0_1$ universal set]
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    The pairs of cylinders in the displayed union are recursively enumerable, so the union is effectively open in the
    product of the discrete space $\omega$ and $\BaireSpace$. Conversely, an effectively open set is given by some
    recursively enumerable list of cylinders, hence by some $W_e$, and therefore equals $U_e$. Equivalently, one may use
    semidecidability: a halting computation reads only finitely much of $p$, so its accepting finite transcripts enumerate
    cylinders. This is the finite-use principle from §{sec:lambda-baire-space}.
-/
/-- Parameter-free effective openness and universality, as used at the first lightface level. -/
theorem sigma01_universal :
    RelativelyEffectivelyOpenNatBaire (fun _ => 0) (effectiveOpenUniversal (fun _ => 0)) ∧
    (∀ e, EffectivelyOpen {p | (e, p) ∈ effectiveOpenUniversal (fun _ => 0)}) ∧
    (∀ U, EffectivelyOpen U → ∃ e, U = {p | (e, p) ∈ effectiveOpenUniversal (fun _ => 0)}) :=
  ⟨effectiveOpenUniversal_effectivelyOpen _, effectiveOpenUniversal_section _,
    effectiveOpenUniversal_universal _⟩

/-- A finite cylinder on which the first-coordinate pullback has accepted.
The nonempty word fixes the index before the acceptance certificate is used. -/
def diagonalOpenWords (ε : ℕ → ℕ) : Set (List ℕ) :=
  {t | t ≠ [] ∧ ∃ s, s.IsPrefix t ∧
    OracleRuns ε (Term.closedProgram (t.headD 0)) (NatListCode.encode s) 1}

/-- A total lambda test searches word/certificate pairs without changing ε. -/
theorem diagonalOpenWords_semidecidable (ε : ℕ → ℕ) :
    LambdaRelative.SemidecidablePredicate ε (· ∈ diagonalOpenWords ε) := by
  have hx := projection_computes true
  have hs := (projection_computes true).comp (projection_computes false)
  have hb := (projection_computes false).comp (projection_computes false)
  have hh : NumericalComputes (listFieldTerm true)
      (fun r => (NatListCode.decode r).headD 0) :=
    ⟨listFieldTerm_closed true, fun r => by
      simpa only [NatListCode.encode_decode, List.headD_eq_getD]
        using listHead_code (NatListCode.decode r)⟩
  have hc := (uniformCandidateProgram_computes ε).reindex
    ((hh.comp hx).pair (hs.pair ((numericalConstant_computes 1).pair hb)))
  have hp := listPrefix_computes.comp (hs.pair hx)
  have hn := reverseZero_computes.comp (reverseZero_computes.comp hx)
  have ht := (hc.pair (LambdaRelative.ofNumerical (hp.mul hn) ε)).map
    ((projection_computes true).mul (projection_computes false))
  refine ⟨relativeSearchProgram _, relativeSearchProgram_closed ht.1, ?_⟩
  intro t
  rw [relativeSearchProgram_runs_iff ht]
  simp only [true_and, show Encodable.encode t = NatListCode.encode t from rfl]
  change (t ≠ [] ∧ ∃ s, s.IsPrefix t ∧
      OracleRuns ε (Term.closedProgram (t.headD 0)) (NatListCode.encode s) 1) ↔ _
  simp only [Nat.unpair_pair, Term.oracleOutputCandidate,
    Bool.false_eq_true, ite_true, ite_false]
  constructor
  · rintro ⟨hne, s, hst, hr⟩
    obtain ⟨b, hb⟩ := (oracle_outputTest_exists_iff ε _ _ 1).mpr hr
    refine ⟨Nat.pair (NatListCode.encode s) b, ?_⟩
    have hcode : NatListCode.encode t ≠ 0 := by
      intro h
      have := congrArg NatListCode.decode h
      exact hne (by simpa [NatListCode.decode] using this)
    simpa [Nat.unpair_pair, NatListCode.decode_encode, hst, hcode, List.headD] using hb
  · rintro ⟨k, hk⟩
    have hcode : NatListCode.encode t ≠ 0 := by
      intro h; simp [h] at hk
    have hst : (NatListCode.decode k.unpair.1).IsPrefix t := by
      by_contra h; simp [h] at hk
    have htest : Term.boundedInputTest ε
        (Term.oracleProgramInput (t.headD 0) k.unpair.1)
        (Term.churchNumeral 1) k.unpair.2 = true := by
      by_contra h
      simp only [List.headD] at h
      simp [List.headD, h] at hk
    refine ⟨fun h => hcode (by simp [h, NatListCode.encode]),
      NatListCode.decode k.unpair.1, hst, ?_⟩
    simpa only [NatListCode.encode_decode] using
      (oracle_outputTest_exists_iff ε _ _ 1).mp ⟨_, htest⟩

/-- The recursive first-coordinate pullback is an effectively open cylinder union. -/
theorem effectiveOpenUniversal_diagonalPreimage (ε : ℕ → ℕ) :
    RelativelyEffectivelyOpen ε {p | (p 0, p) ∈ effectiveOpenUniversal ε} := by
  refine ⟨diagonalOpenWords ε, diagonalOpenWords_semidecidable ε, ?_⟩
  ext p
  rw [mem_cylinderCode]
  change p ∈ cylinderCode (universalOpenWords ε (p 0)) ↔ _
  rw [mem_cylinderCode]
  constructor
  · rintro ⟨s, hs, hsp⟩
    let n := max 1 s.length
    let t := seqPrefix p n
    have ht : t ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [t, seqPrefix_length, List.length_nil] at this
      omega
    have hst : s.IsPrefix t := by
      rw [← seqPrefix_eq_of_mem_cyl hsp]
      exact seqPrefix_prefixOf_of_le p (le_max_right 1 s.length)
    have hhead : t.headD 0 = p 0 := by
      cases h : t with
      | nil => exact False.elim (ht h)
      | cons a l =>
        have hp : prefixOfSeq t p := prefixOfSeq_seqPrefix p n
        have hp0 := hp 0 (by simp [h])
        simpa [h] using hp0.symm
    exact ⟨t, ⟨ht, s, hst, by
      rw [hhead]
      exact hs⟩,
      prefixOfSeq_seqPrefix p n⟩
  · rintro ⟨t, ⟨ht, s, hst, hs⟩, htp⟩
    have hhead : t.headD 0 = p 0 := by
      cases t with
      | nil => exact False.elim (ht rfl)
      | cons a l => simpa using (htp 0 (by simp)).symm
    refine ⟨s, ?_, prefixOfSeq_of_prefix hst htp⟩
    change OracleRuns ε (Term.closedProgram (p 0)) (NatListCode.encode s) 1
    rw [hhead] at hs
    exact hs

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For the universal set above, put
    $$D \;:=\; \{p \in \BaireSpace : (p(0), p) \notin U\}.$$
    The complement of $D$ is the recursive preimage of $U$ under $p\mapsto(p(0),p)$, so it is $\lSigma^0_1$ and $D$ is
    $\lPi^0_1$. If $D$ were also $\lSigma^0_1$, universality would make it a section $U_{e_0}$, contradicting the
    first-coordinate diagonal lemma.
-/
/-- The diagonal is relatively effectively closed but escapes every open section. -/
theorem firstLightfaceStrictness_relative (ε : ℕ → ℕ) :
    ∃ D, RelativelyEffectivelyClosed ε D ∧ ¬ RelativelyEffectivelyOpen ε D := by
  let U : ℕ → Set (ℕ → ℕ) := fun e => {p | (e, p) ∈ effectiveOpenUniversal ε}
  refine ⟨firstCoordinateDiagonal U, ?_, ?_⟩
  · change RelativelyEffectivelyOpen ε (firstCoordinateDiagonal U)ᶜ
    convert effectiveOpenUniversal_diagonalPreimage ε using 1
    ext p
    simp [firstCoordinateDiagonal, U]
  · intro hD
    obtain ⟨e, he⟩ := effectiveOpenUniversal_universal ε _ hD
    exact firstCoordinateDiagonal_ne_section U e he

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  excerpt: |
    \begin{theorem*}[Strictness at the first lightface level]
-/
/-- Strictness at the first lightface level with the computable zero parameter. -/
theorem firstLightfaceStrictness : ∃ D, EffectivelyClosed D ∧ ¬ EffectivelyOpen D :=
  firstLightfaceStrictness_relative (fun _ => 0)

end PolishSpaceBook
