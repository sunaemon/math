module

public import PolishSpaceBook.LambdaFiniteUniversal
public import PolishSpaceBook.FiniteBorelUniversal

@[expose] public section

/-! # Finite Borel classes are the union of their lightface relativizations

One real stores the cylinder predicates of every numerical row. One closed
lambda search program reads that table and the point. The parameter exists
mathematically; no computable selection of a parameter from an open set is
asserted.
-/
noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
open scoped Ordinal
namespace LambdaFinite

local instance relativeMatrixWords : Encodable (List ℕ) := NatListCode.encodable

@[reducible] def matrixWordEncoding : Encodable (ℕ × List ℕ) where
  encode z := Nat.pair z.1 (NatListCode.encode z.2)
  decode n := some (n.unpair.1, NatListCode.decode n.unpair.2)
  encodek z := by simp
local instance relativeMatrixWordPairs : Encodable (ℕ × List ℕ) := matrixWordEncoding

/-- The supplied decider is joint in the context and finite word. Search
only the length of the point prefix, retaining the original parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{boldface class}{boldface classes} are recovered by **\termforward{relativization}**. Fix a real
    $a \in \BaireSpace$
    and allow all algorithms and recursive predicates in the preceding definitions to use $a$ as an input function.
    Concretely, a relative computation may ask for the value $a(n)$ at any natural number $n$ during its finite computation.
    Thus $a$ acts as a fixed infinite table of background information.
-/
theorem open_matrix_program {ε : ℕ → ℕ} {D : AlphaTerm} {W : Set (ℕ × List ℕ)}
    (hD : LambdaRelative.Decides ε D (· ∈ W)) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ z p,
      (∃ s, (z, s) ∈ W ∧ prefixOfSeq s p) ↔ matrixDomain ε P z p := by
  classical
  have hd : LambdaRelative.Computes ε D
      (fun z : ℕ => if (z.unpair.1, NatListCode.decode z.unpair.2) ∈ W then 1 else 0) := by
    refine ⟨hD.1, fun z => ?_⟩
    have hz := hD.runs (z.unpair.1, NatListCode.decode z.unpair.2)
    change OracleRuns ε D (Nat.pair z.unpair.1 (NatListCode.encode (NatListCode.decode z.unpair.2))) _ at hz
    simpa only [NatListCode.encode_decode, Nat.pair_unpair, Encodable.encode_nat] using hz
  let E := LambdaTree.parameterProjectionProgram true
  let X := LambdaTree.parameterProjectionProgram false
  let T := relativeComposeProgram (compositionProgram D E)
    (pairOutputProgram (liftNumericalProgram (numericalProjectionTerm true))
      (reindexProgram (compositionProgram prefixProgram X) (numericalProjectionTerm false)))
  have ht (p : ℕ → ℕ) : LambdaRelative.Computes (LambdaTree.sectionParameter ε p) T
      (fun z : ℕ => if (z.unpair.1, seqPrefix p z.unpair.2) ∈ W then 1 else 0) := by
    have he := LambdaTree.parameterProjection_computes true ε p
    have hx := LambdaTree.parameterProjection_computes false ε p
    have hp := open_computes_changeParameter
      (⟨prefixProgram_closed, fun n => prefixProgram_runs p n⟩ :
        LambdaRelative.Computes p prefixProgram (fun n : ℕ => NatListCode.encode (seqPrefix p n))) hx
    have h := (open_computes_changeParameter hd he).comp
      ((LambdaRelative.ofNumerical (projection_computes true) (LambdaTree.sectionParameter ε p)).pair
        (hp.reindex (projection_computes false)))
    simpa only [T, E, X, Nat.unpair_pair, NatListCode.decode_encode,
      ite_true, Bool.false_eq_true, ite_false] using h
  refine ⟨relativeSearchProgram T, relativeSearchProgram_closed (ht (fun _ => 0)).1, fun z p => ?_⟩
  simp only [matrixDomain, relativeSearchProgram_runs_iff (ht p), Nat.unpair_pair]
  have hh : (∃ s, (z, s) ∈ W ∧ prefixOfSeq s p) ↔ ∃ k, (z, seqPrefix p k) ∈ W := by
    constructor
    · rintro ⟨s, hs, hp⟩
      exact ⟨s.length, by simpa only [seqPrefix_eq_of_mem_cyl hp] using hs⟩
    · rintro ⟨k, hk⟩
      exact ⟨seqPrefix p k, hk, prefixOfSeq_seqPrefix p k⟩
  simpa using hh

/-- Every row is open. A single parameter codes all row-cylinder predicates,
and the preceding construction supplies one closed matrix program. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{boldface class}{boldface classes} are recovered by **\termforward{relativization}**. Fix a real
    $a \in \BaireSpace$
    and allow all algorithms and recursive predicates in the preceding definitions to use $a$ as an input function.
    Concretely, a relative computation may ask for the value $a(n)$ at any natural number $n$ during its finite computation.
    Thus $a$ acts as a fixed infinite table of background information.
-/
theorem open_matrix_one_parameter (U : ℕ → Set (ℕ → ℕ)) (hU : ∀ z, IsOpen (U z)) :
    ∃ (ε : ℕ → ℕ) (P : AlphaTerm), P.Closed ∧ ∀ z p, p ∈ U z ↔ matrixDomain ε P z p := by
  let W : Set (ℕ × List ℕ) := {z | z.2 ∈ openCylinderCode (U z.1)}
  obtain ⟨ε, hε⟩ := LambdaRelative.predicates_in_one_parameter (fun _ : ℕ => fun z => z ∈ W)
  obtain ⟨P, hP, h⟩ := open_matrix_program (hε 0)
  refine ⟨ε, P, hP, fun z p => ?_⟩
  rw [← open_eq_cylinderCode_openCylinderCode (hU z), mem_cylinderCode]
  exact h z p

theorem matrixDomain_isOpen (ε : ℕ → ℕ) (P : AlphaTerm) (z : ℕ) :
    IsOpen {p | matrixDomain ε P z p} := by
  have hc : Continuous (LambdaTree.sectionParameter ε) := by
    apply continuous_pi
    intro i
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => Nat.pair (ε i) k)).comp
      (continuous_apply i)
  have he : {p | matrixDomain ε P z p} =
      ⋃ m : ℕ, (LambdaTree.sectionParameter ε) ⁻¹' {q | OracleRuns q P z m} := by
    ext p
    simp only [matrixDomain, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [he]
  exact isOpen_iUnion (fun m => (isOpen_oracleRuns P z m).preimage hc)

/-- The same recursive operations give the canonical positive Borel level. -/
theorem alternating_mem_borelSigma (n : ℕ) (R : ℕ → (ℕ → ℕ) → Prop)
    (hR : ∀ z, IsOpen {p | R z p}) (z : ℕ) :
    {p | alternating n R z p} ∈ borelSigma (↑n + 1) := by
  let := TopologicalSpace.metrizableSpaceMetric (ℕ → ℕ)
  induction n generalizing z with
  | zero => simpa only [Nat.cast_zero, zero_add, borelSigma_one, Set.mem_ofPred_eq, alternating] using hR z
  | succ n ih =>
    rw [Nat.cast_succ, borelSigma_succ_iff (by exact le_add_left le_rfl)]
    refine ⟨fun k => ({p | alternating n R (Nat.pair z k) p})ᶜ, ?_, ?_⟩
    · intro k
      simpa only [borelPi, Set.mem_ofPred_eq, compl_compl] using ih (Nat.pair z k)
    · ext p
      simp only [alternating, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_compl_iff]

/-- Row choices are packed at the mathematical matrix level. Only after all
rows have been combined is one oracle selected for that entire open matrix. -/
theorem borelSigma_open_matrix (n : ℕ) (A : Set (ℕ → ℕ))
    (hA : A ∈ borelSigma (↑n + 1)) :
    ∃ R : ℕ → (ℕ → ℕ) → Prop, (∀ z, IsOpen {p | R z p}) ∧
      ∀ p, p ∈ A ↔ alternating n R 0 p := by
  classical
  let := TopologicalSpace.metrizableSpaceMetric (ℕ → ℕ)
  induction n generalizing A with
  | zero =>
    refine ⟨fun _ p => p ∈ A, fun _ => ?_, fun _ => Iff.rfl⟩
    simpa only [Nat.cast_zero, zero_add, borelSigma_one, Set.mem_ofPred_eq, Set.ofPred_mem_eq] using hA
  | succ n ih =>
    rw [Nat.cast_succ, borelSigma_succ_iff (by exact le_add_left le_rfl)] at hA
    obtain ⟨F, hF, rfl⟩ := hA
    choose R hR hEq using fun k => ih (F k)ᶜ (hF k)
    let S : ℕ → (ℕ → ℕ) → Prop := fun z p =>
      R (contextRoot n z).unpair.2 (mapContext n (fun _ => 0) z) p
    refine ⟨S, fun z => hR _ _, fun p => ?_⟩
    simp only [Set.mem_iUnion, alternating]
    apply exists_congr
    intro k
    have hr := alternating_root n R (fun a => a.unpair.2) (fun _ => 0) (Nat.pair 0 k) p
    simp only [Nat.unpair_pair] at hr
    have hk : p ∈ F k ↔ ¬ alternating n (R k) 0 p := by
      simpa only [Set.mem_compl_iff, not_not] using not_congr (hEq k p)
    exact hk.trans (not_congr hr).symm

theorem sigma_mem_borelSigma {ε : ℕ → ℕ} {n : ℕ} {A : Set (ℕ → ℕ)}
    (hA : Sigma ε n A) : A ∈ borelSigma (↑n + 1) := by
  obtain ⟨P, _, h⟩ := hA
  have he : A = {p | alternating n (matrixDomain ε P) 0 p} := Set.ext h
  rw [he]
  exact alternating_mem_borelSigma n _ (matrixDomain_isOpen ε P) 0

/-- The full finite-level relativization theorem uses one original parameter
and one closed matrix, jointly in every numerical context. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The resulting relativized classes are denoted $\lSigma^k_n(a)$, $\lPi^k_n(a)$, and $\lDelta^k_n(a)$. Then
    $$\bSigma^k_n \;=\; \bigcup_{a \in \BaireSpace} \lSigma^k_n(a).$$
    The slogan is *boldface = lightface relativized to all real parameters*.
-/
theorem borelSigma_iff_exists_sigma (n : ℕ) (A : Set (ℕ → ℕ)) :
    A ∈ borelSigma (↑n + 1) ↔ ∃ ε, Sigma ε n A := by
  constructor
  · intro hA
    obtain ⟨R, hR, hEq⟩ := borelSigma_open_matrix n A hA
    obtain ⟨ε, P, hP, h⟩ := open_matrix_one_parameter (fun z => {p | R z p}) hR
    refine ⟨ε, P, hP, fun p => (hEq p).trans ?_⟩
    exact alternating_congr n h 0 p
  · rintro ⟨ε, hA⟩
    exact sigma_mem_borelSigma hA

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The resulting relativized classes are denoted $\lSigma^k_n(a)$, $\lPi^k_n(a)$, and $\lDelta^k_n(a)$. Then
    $$\bSigma^k_n \;=\; \bigcup_{a \in \BaireSpace} \lSigma^k_n(a).$$
    The slogan is *boldface = lightface relativized to all real parameters*.
-/
theorem borelPi_iff_exists_pi (n : ℕ) (A : Set (ℕ → ℕ)) :
    A ∈ borelPi (↑n + 1) ↔ ∃ ε, Pi ε n A := borelSigma_iff_exists_sigma n Aᶜ

/-- A countable family at one finite level admits one common real and one
closed matrix program. The section index stays in the numerical context. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This slogan should be read literally. A boldface open set may require a noncomputable list of cylinders. Treat that list
    as a real parameter $a$, give the program input-function access to $a$, and the same set becomes lightface relative to
    $a$. The topological hierarchy is therefore the union of all its computable versions relative to all possible real
    parameters.
-/
theorem borelSigma_family_one_parameter (n : ℕ) (A : ℕ → Set (ℕ → ℕ))
    (hA : ∀ k, A k ∈ borelSigma (↑n + 1)) :
    ∃ ε, UniformSigma ε n A := by
  classical
  choose R hR hEq using fun k => borelSigma_open_matrix n (A k) (hA k)
  let S : ℕ → (ℕ → ℕ) → Prop := fun z p =>
    R (contextRoot n z) (mapContext n (fun _ => 0) z) p
  obtain ⟨ε, P, hP, h⟩ := open_matrix_one_parameter (fun z => {p | S z p}) (fun z => hR _ _)
  refine ⟨ε, P, hP, fun k p => ?_⟩
  have hr := alternating_root n R id (fun _ => 0) k p
  exact (hEq k p).trans (hr.symm.trans (alternating_congr n h k p))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The resulting relativized classes are denoted $\lSigma^k_n(a)$, $\lPi^k_n(a)$, and $\lDelta^k_n(a)$. Then
    $$\bSigma^k_n \;=\; \bigcup_{a \in \BaireSpace} \lSigma^k_n(a).$$
    The slogan is *boldface = lightface relativized to all real parameters*.
-/
theorem borelDelta_iff_exists_delta (n : ℕ) (A : Set (ℕ → ℕ)) :
    A ∈ borelDelta (↑n + 1) ↔ ∃ ε, Delta ε n A := by
  classical
  constructor
  · intro hA
    have hS : A ∈ borelSigma (↑n + 1) := hA.1
    have hP : Aᶜ ∈ borelSigma (↑n + 1) := hA.2
    let F : ℕ → Set (ℕ → ℕ) := fun k => if k = 0 then A else Aᶜ
    have hF (k) : F k ∈ borelSigma (↑n + 1) := by
      by_cases hk : k = 0
      · simpa only [F, hk, ite_true] using hS
      · simpa only [F, hk, ite_false] using hP
    obtain ⟨ε, hε⟩ := borelSigma_family_one_parameter n F hF
    refine ⟨ε, ?_, ?_⟩
    · simpa only [F, ite_true] using hε.section 0
    · simpa only [Pi, F, show (1 : ℕ) ≠ 0 from by decide, ite_false] using hε.section 1
  · rintro ⟨ε, hS, hP⟩
    exact ⟨sigma_mem_borelSigma hS, sigma_mem_borelSigma hP⟩

end LambdaFinite
end PolishSpaceBook
