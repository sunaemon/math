module

public import PolishSpaceBook.LambdaComputability
public import PolishSpaceBook.LambdaHaltingObstruction
public import PolishSpaceBook.LambdaListAccess
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # A binary-word halting language with an actual lambda semidecider

The pair (e,n) is represented by the binary word consisting of pair(e,n) zero
bits. Length decodes its pair index. Other finite words are rejected by the
finite equality test before the output-certificate search succeeds.
-/

namespace PolishSpaceBook.LambdaHaltingLanguage
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
set_option maxRecDepth 4096

def zeroWordCode : ℕ → ℕ := primitiveRec 0 (fun _ r => Nat.pair 0 r + 1)

theorem zeroWordCode_eq (n : ℕ) :
    zeroWordCode n = NatListCode.encode (List.replicate n 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [zeroWordCode, primitiveRec, List.replicate_succ, NatListCode.encode] using
      congrArg (fun r => Nat.pair 0 r + 1) ih

theorem zeroWordCode_length (n : ℕ) : (NatListCode.decode (zeroWordCode n)).length = n := by
  rw [zeroWordCode_eq, NatListCode.decode_encode, List.length_replicate]

def binaryPairWord (e n : ℕ) : List Bool := List.replicate (Nat.pair e n) false

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The same argument gives the usual halting language. Using a computable binary-string code
    $\langle e,n\rangle_2\in\finseq{2}$ for pairs of natural numbers, set
    $$
    H:=\{\langle e,n\rangle_2\in\finseq{2}:\varphi_e(n)\downarrow\}.
    $$
    Then $H$ is recursively enumerable, because the universal evaluator semidecides it, but $H$ is not decidable.
-/
theorem binaryPairWord_code (e n : ℕ) :
    NatListCode.encode ((binaryPairWord e n).map Bool.toNat) = zeroWordCode (Nat.pair e n) := by
  simp [binaryPairWord, zeroWordCode_eq]

def prependZeroProgram : AlphaTerm :=
  numericalCombine listConsTerm (numericalConstant 0) numericalIdentity

theorem prependZeroProgram_computes :
    NumericalComputes prependZeroProgram (fun r => Nat.pair 0 r + 1) :=
  (numericalConstant_computes 0).combine numericalIdentity_computes listConsTerm_closed
    (fun a r => Nat.pair a r + 1) listConsTerm_apply

def zeroWordProgram : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant 0)
    (numericalCompose prependZeroProgram
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))))
  (pairNumerical (numericalConstant 0) numericalIdentity)

theorem zeroWordProgram_computes : NumericalComputes zeroWordProgram zeroWordCode := by
  have hh := prependZeroProgram_computes.comp ((projection_computes false).comp (projection_computes false))
  have hr := (numericalRecursion_computes (numericalConstant_computes 0) hh).comp
    ((numericalConstant_computes 0).pair numericalIdentity_computes)
  simpa only [zeroWordProgram, zeroWordCode, Nat.unpair_pair, Bool.false_eq_true, ite_false, id_eq] using hr

/-- The code check rejects all words other than the chosen binary pair encodings. -/
def haltingLanguage : Set ℕ := {w |
  w = zeroWordCode (NatListCode.decode w).length ∧
    ∃ m, App (NatListCode.decode w).length.unpair.1 (NatListCode.decode w).length.unpair.2 m}

@[simp] theorem code_mem_haltingLanguage (e n : ℕ) :
    zeroWordCode (Nat.pair e n) ∈ haltingLanguage ↔ ∃ m, App e n m := by
  change (_ = _ ∧ _) ↔ _
  simp only [zeroWordCode_length, Nat.unpair_pair, true_and]

theorem mem_haltingLanguage_iff (w : ℕ) : w ∈ haltingLanguage ↔
    ∃ e n, w = NatListCode.encode ((binaryPairWord e n).map Bool.toNat) ∧ ∃ m, App e n m := by
  constructor
  · rintro ⟨hw, hh⟩
    refine ⟨(NatListCode.decode w).length.unpair.1, (NatListCode.decode w).length.unpair.2, ?_, hh⟩
    rw [binaryPairWord_code, Nat.pair_unpair]
    exact hw
  · rintro ⟨e, n, rfl, hh⟩
    rw [binaryPairWord_code, code_mem_haltingLanguage]
    exact hh

def stageValue (z : ℕ) : ℕ :=
  (if z.unpair.1 = zeroWordCode (NatListCode.decode z.unpair.1).length then 1 else 0) *
    (if Term.outputCandidate (NatListCode.decode z.unpair.1).length.unpair.1
      (NatListCode.decode z.unpair.1).length.unpair.2 z.unpair.2 then 1 else 0)

def stageProgram : AlphaTerm :=
  let W := numericalProjectionTerm true
  let L := numericalCompose listLengthTerm W
  mulNumerical (numericalCombine equalityTerm W (numericalCompose zeroWordProgram L))
    (numericalApply3 outputCandidateTerm (numericalCompose (numericalProjectionTerm true) L)
      (numericalCompose (numericalProjectionTerm false) L) (numericalProjectionTerm false))

theorem stageProgram_computes : NumericalComputes stageProgram stageValue := by
  have hL := listLength_computes.comp (projection_computes true)
  have hg := (projection_computes true).combine (zeroWordProgram_computes.comp hL)
    equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  have ht := ((projection_computes true).comp hL).apply3
    ((projection_computes false).comp hL) (projection_computes false) outputCandidateTerm_closed
    (fun e n k => if Term.outputCandidate e n k then 1 else 0) outputCandidateTerm_apply
  exact hg.mul ht

lemma halts_iff_candidate (e n : ℕ) :
    (∃ m, App e n m) ↔ ∃ k, Term.outputCandidate e n k = true := by
  simp only [App, program_output_iff_candidate, outputCandidate_accept_iff]
  constructor
  · rintro ⟨m, k, _, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k.unpair.1, k, rfl, hk⟩

def semidecider : AlphaTerm := numericalSearch stageProgram

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The same argument gives the usual halting language. Using a computable binary-string code
    $\langle e,n\rangle_2\in\finseq{2}$ for pairs of natural numbers, set
    $$
    H:=\{\langle e,n\rangle_2\in\finseq{2}:\varphi_e(n)\downarrow\}.
    $$
    Then $H$ is recursively enumerable, because the universal evaluator semidecides it, but $H$ is not decidable.
-/
theorem semidecider_exact (w : ℕ) :
    (∃ m, Relation.ReflTransGen Beta (app semidecider (numeral w)) (numeral m)) ↔ w ∈ haltingLanguage := by
  rw [semidecider, numericalSearch_domain stageProgram_computes]
  have hs (k : ℕ) : stageValue (Nat.pair w k) ≠ 0 ↔
      w = zeroWordCode (NatListCode.decode w).length ∧
        Term.outputCandidate (NatListCode.decode w).length.unpair.1
          (NatListCode.decode w).length.unpair.2 k = true := by
    simp [stageValue, Nat.unpair_pair, and_comm]
  simp_rw [hs]
  change (∃ k, _ ∧ _) ↔ _ ∧ _
  rw [exists_and_left, halts_iff_candidate]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The same argument gives the usual halting language. Using a computable binary-string code
    $\langle e,n\rangle_2\in\finseq{2}$ for pairs of natural numbers, set
    $$
    H:=\{\langle e,n\rangle_2\in\finseq{2}:\varphi_e(n)\downarrow\}.
    $$
    Then $H$ is recursively enumerable, because the universal evaluator semidecides it, but $H$ is not decidable.
-/
theorem haltingLanguage_enumerable : LambdaEnumerable haltingLanguage :=
  (lambdaEnumerable_iff haltingLanguage).mpr
    ⟨semidecider, numericalSearch_closed stageProgram_computes.1, semidecider_exact⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Undecidability of halting.** The \termdefine{halting problem} concerns the set
        $$
        K=\{e:\varphi_e(e)\downarrow\}
        $$
        which is recursively enumerable but not decidable.
-/
theorem diagonalHalts_enumerable : LambdaEnumerable {e | diagonalHalts e} := by
  have hdiag := zeroWordProgram_computes.comp (numericalIdentity_computes.pair numericalIdentity_computes)
  have he : (fun e => zeroWordCode (Nat.pair e e)) ⁻¹' haltingLanguage = {e | diagonalHalts e} := by
    ext e
    exact code_mem_haltingLanguage e e
  exact he ▸ haltingLanguage_enumerable.preimage hdiag

noncomputable local instance (e n : ℕ) : Decidable (∃ m, App e n m) := Classical.propDecidable _

/-- Even a program required to answer only on the chosen binary pair words is
impossible. Thus the obstruction also applies to deciders with binary-word domain. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The same argument gives the usual halting language. Using a computable binary-string code
    $\langle e,n\rangle_2\in\finseq{2}$ for pairs of natural numbers, set
    $$
    H:=\{\langle e,n\rangle_2\in\finseq{2}:\varphi_e(n)\downarrow\}.
    $$
    Then $H$ is recursively enumerable, because the universal evaluator semidecides it, but $H$ is not decidable.
-/
theorem no_decider_on_binary_pair_words : ¬ ∃ D : AlphaTerm, D.Closed ∧ ∀ e n : ℕ,
    Relation.ReflTransGen Beta
      (app D (numeral (zeroWordCode (Nat.pair e n))))
      (numeral (if ∃ m, App e n m then 1 else 0)) := by
  classical
  rintro ⟨D, hc, hd⟩
  have hdiag := zeroWordProgram_computes.comp (numericalIdentity_computes.pair numericalIdentity_computes)
  let G := numericalCompose zeroWordProgram (pairNumerical numericalIdentity numericalIdentity)
  have hG : G.Closed := hdiag.1
  have hDG : NumericalComputes (numericalCompose D G)
      (fun e => if diagonalHalts e then 1 else 0) := by
    refine ⟨?_, fun e => ?_⟩
    · unfold numericalCompose Closed
      simp only [fv_lam, fv_app, fv_var]
      rw [hc, hdiag.1]
      simp
    · have hb : Beta (app (numericalCompose D G) (numeral e))
          (app D (app G (numeral e))) := by
        simpa only [numericalCompose, subst_app, subst_var, ite_true,
          subst_closed _ _ _ hc, subst_closed _ _ _ hG] using
          Beta.contract 40 (app D (app G (var 40))) (numeral e)
      exact (Relation.ReflTransGen.single hb).trans
        ((beta_steps_app_right D (hdiag.2 e)).trans (hd e e))
  have h := reverseZero_computes.comp hDG
  apply diagonalHalts_not_decidable
  refine ⟨_, ⟨h.1, fun e => ?_⟩⟩
  have he := h.2 e
  by_cases hh : diagonalHalts e <;>
    simpa only [hh, ite_true, ite_false,
      Nat.one_ne_zero, ↓reduceIte] using he

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The same argument gives the usual halting language. Using a computable binary-string code
    $\langle e,n\rangle_2\in\finseq{2}$ for pairs of natural numbers, set
    $$
    H:=\{\langle e,n\rangle_2\in\finseq{2}:\varphi_e(n)\downarrow\}.
    $$
    Then $H$ is recursively enumerable, because the universal evaluator semidecides it, but $H$ is not decidable.
-/
theorem haltingLanguage_not_decidable : ¬ LambdaDecidable haltingLanguage := by
  classical
  rintro ⟨D, hd⟩
  apply no_decider_on_binary_pair_words
  exact ⟨D, hd.1, fun e n => by
    simpa only [code_mem_haltingLanguage] using hd.2 (zeroWordCode (Nat.pair e n))⟩

end PolishSpaceBook.LambdaHaltingLanguage
