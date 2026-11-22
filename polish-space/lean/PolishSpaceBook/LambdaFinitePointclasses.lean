module

public import PolishSpaceBook.LambdaEffectiveOpenCoding
public import PolishSpaceBook.BairePairGeometry

@[expose] public section

/-! # Finite lightface pointclasses with one uniform lambda matrix

The internal level n denotes the positive level n + 1. All natural-number
quantifiers are stored in the numerical input of one closed matrix program.
The same real parameter is retained at every level and in every row.
-/
noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaFinite

/-- A total lambda input translator preserves the whole numerical halting
 domain. Search over finite certificates supplies both implications. -/
theorem domain_reindex {P G : AlphaTerm} (hP : P.Closed)
    {g : (ℕ → ℕ) → ℕ → ℕ} (hG : UniformNumericalComputes G g) :
    ∃ Q : AlphaTerm, Q.Closed ∧ ∀ q n,
      (∃ m, OracleRuns q Q n m) ↔ ∃ m, OracleRuns q P (g q n) m := by
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  let T := relativeComposeProgram (candidateTestProgram e)
    (pairOutputProgram (reindexProgram G (numericalProjectionTerm true))
      (liftNumericalProgram (numericalProjectionTerm false)))
  have ht (q : ℕ → ℕ) : LambdaRelative.Computes q T
      (fun z : ℕ => if candidateTest q e (Nat.pair (g q z.unpair.1) z.unpair.2) then 1 else 0) := by
    have hc : LambdaRelative.Computes q (candidateTestProgram e)
        (fun z : ℕ => if candidateTest q e z then 1 else 0) :=
      ⟨(candidateTestProgram_computes e).1, (candidateTestProgram_computes e).2 q⟩
    have hg : LambdaRelative.Computes q G (g q) := ⟨hG.1, hG.2 q⟩
    simpa only [T, ite_true, Bool.false_eq_true, ite_false] using
      hc.comp ((hg.reindex (projection_computes true)).pair
        (LambdaRelative.ofNumerical (projection_computes false) q))
  refine ⟨relativeSearchProgram T, relativeSearchProgram_closed (ht (fun _ => 0)).1, fun q n => ?_⟩
  simp only [relativeSearchProgram_runs_iff (ht q), Nat.unpair_pair]
  have h := LambdaRelative.candidateTest_exists_iff q e (g q n)
  rw [he] at h
  simpa using h

/-- Replace the initial context, preserving the n subsequently paired digits. -/
def mapContext : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, f, z => f z
  | n + 1, f, z => Nat.pair (mapContext n f z.unpair.1) z.unpair.2

def mapContextProgram : ℕ → AlphaTerm → AlphaTerm
  | 0, F => F
  | n + 1, F => pairNumerical
      (numericalCompose (mapContextProgram n F) (numericalProjectionTerm true))
      (numericalProjectionTerm false)

theorem mapContextProgram_computes {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) (n : ℕ) :
    NumericalComputes (mapContextProgram n F) (mapContext n f) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    simpa only [mapContextProgram, mapContext, ite_true, Bool.false_eq_true, ite_false] using
      (ih.comp (projection_computes true)).pair (projection_computes false)

theorem mapContext_succ_right (n : ℕ) (f : ℕ → ℕ) (z : ℕ) :
    mapContext (n + 1) f z = mapContext n
      (fun a => Nat.pair (f a.unpair.1) a.unpair.2) z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change Nat.pair (mapContext (n + 1) f z.unpair.1) z.unpair.2 = _
    rw [ih]
    rfl

/-- Each successor adds one existential quantifier and reverses polarity. -/
def alternating : ℕ → (ℕ → (ℕ → ℕ) → Prop) → ℕ → (ℕ → ℕ) → Prop
  | 0, R, z, p => R z p
  | n + 1, R, z, p => ∃ k, ¬ alternating n R (Nat.pair z k) p

theorem alternating_congr (n : ℕ) {R S : ℕ → (ℕ → ℕ) → Prop}
    (h : ∀ z p, R z p ↔ S z p) (z : ℕ) (p : ℕ → ℕ) :
    alternating n R z p ↔ alternating n S z p := by
  induction n generalizing z with
  | zero => exact h z p
  | succ n ih => exact exists_congr (fun k => not_congr (ih (Nat.pair z k)))

theorem alternating_congr_point (n : ℕ) {R S : ℕ → (ℕ → ℕ) → Prop}
    (z : ℕ) (p : ℕ → ℕ) (h : ∀ a, R a p ↔ S a p) :
    alternating n R z p ↔ alternating n S z p := by
  induction n generalizing z with
  | zero => exact h z
  | succ n ih => exact exists_congr (fun k => not_congr (ih (Nat.pair z k)))

theorem alternating_reindex (n : ℕ) (R : ℕ → (ℕ → ℕ) → Prop)
    (f : ℕ → ℕ) (z : ℕ) (p : ℕ → ℕ) :
    alternating n (fun a => R (mapContext n f a)) z p ↔ alternating n R (f z) p := by
  induction n generalizing f z with
  | zero => rfl
  | succ n ih =>
    change (∃ k, ¬ alternating n (fun a => R (mapContext (n + 1) f a)) (Nat.pair z k) p) ↔ _
    simp only [mapContext_succ_right]
    exact exists_congr (fun k => not_congr (by simpa only [Nat.unpair_pair] using
      (ih (fun a => Nat.pair (f a.unpair.1) a.unpair.2) (Nat.pair z k))))

/-- The parameter and point remain in separate coordinates of the input name. -/
def matrixDomain (ε : ℕ → ℕ) (P : AlphaTerm) (z : ℕ) (p : ℕ → ℕ) : Prop :=
  ∃ m, OracleRuns (LambdaTree.sectionParameter ε p) P z m

/-- Sigma at positive finite level n + 1. -/
def Sigma (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  ∃ P : AlphaTerm, P.Closed ∧ ∀ p, p ∈ A ↔ alternating n (matrixDomain ε P) 0 p

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lPi^0_n$: complements of $\lSigma^0_n$ sets.
-/
def Pi (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) : Prop := Sigma ε n Aᶜ

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lDelta^k_n \;=\; \lSigma^k_n \cap \lPi^k_n$.
-/
def Delta (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  Sigma ε n A ∧ Pi ε n A

/-- Uniformity means that k is another input to one closed matrix program. -/
def UniformSigma (ε : ℕ → ℕ) (n : ℕ) (F : ℕ → Set (ℕ → ℕ)) : Prop :=
  ∃ P : AlphaTerm, P.Closed ∧ ∀ k p, p ∈ F k ↔ alternating n (matrixDomain ε P) k p

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lSigma^0_{n+1}$: effective countable unions of uniformly $\lPi^0_n$ sets; equivalently, sets of the form
        $\{p:\exists k\;(k,p)\in P\}$ for a $\lPi^0_n$ set $P\IncludedIn\omega\times\BaireSpace$.
-/
def UniformPi (ε : ℕ → ℕ) (n : ℕ) (F : ℕ → Set (ℕ → ℕ)) : Prop :=
  UniformSigma ε n (fun k => (F k)ᶜ)

/-- Numerical substitution under all remaining quantifiers is compiled into
one closed program. It does not choose a separate program for each context. -/
theorem matrix_reindex (ε : ℕ → ℕ) (n : ℕ) {P F : AlphaTerm} {f : ℕ → ℕ}
    (hP : P.Closed) (hF : NumericalComputes F f) :
    ∃ Q : AlphaTerm, Q.Closed ∧ ∀ z p,
      alternating n (matrixDomain ε Q) z p ↔ alternating n (matrixDomain ε P) (f z) p := by
  obtain ⟨Q, hQ, h⟩ := domain_reindex hP (mapContextProgram_computes hF n).uniform
  refine ⟨Q, hQ, fun z p => ?_⟩
  exact (alternating_congr n (fun a p => h (LambdaTree.sectionParameter ε p) a) z p).trans
    (alternating_reindex n (matrixDomain ε P) f z p)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lSigma^0_1$: the *effectively open* sets — those expressible as $\bigcup_{e \in W} \cyl{\sigma(e)}$ for a
        recursively enumerable index set $W \IncludedIn \omega$ and a fixed recursive enumeration $\sigma : \omega \to
        \finseq{\omega}$ of finite sequences.
-/
theorem sigma_zero_iff (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    Sigma ε 0 A ↔ RelativelyEffectivelyOpen ε A := by
  rw [relativelyEffectivelyOpen_iff_name_semidecidable]
  constructor
  · rintro ⟨P, hP, h⟩
    exact ⟨P, hP, fun p => (h p).symm⟩
  · rintro ⟨P, hP, h⟩
    exact ⟨P, hP, fun p => (h p).symm⟩

theorem pi_zero_iff (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    Pi ε 0 A ↔ RelativelyEffectivelyClosed ε A := sigma_zero_iff ε Aᶜ

/-- This is exactly the effective countable-union clause with one joint
matrix for the complementary sections, at the original fixed parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lSigma^0_{n+1}$: effective countable unions of uniformly $\lPi^0_n$ sets; equivalently, sets of the form
        $\{p:\exists k\;(k,p)\in P\}$ for a $\lPi^0_n$ set $P\IncludedIn\omega\times\BaireSpace$.
-/
theorem sigma_succ_iff (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) :
    Sigma ε (n + 1) A ↔
      ∃ F : ℕ → Set (ℕ → ℕ), UniformPi ε n F ∧ A = ⋃ k, F k := by
  constructor
  · rintro ⟨P, hP, h⟩
    obtain ⟨Q, hQ, hQP⟩ := matrix_reindex ε n hP
      ((numericalConstant_computes 0).pair numericalIdentity_computes)
    let F : ℕ → Set (ℕ → ℕ) := fun k =>
      {p | ¬ alternating n (matrixDomain ε P) (Nat.pair 0 k) p}
    refine ⟨F, ⟨Q, hQ, fun k p => ?_⟩, ?_⟩
    · exact not_not.trans (hQP k p).symm
    · ext p
      simpa only [Set.mem_iUnion, F, Set.mem_ofPred_eq, alternating] using h p
  · rintro ⟨F, ⟨P, hP, h⟩, rfl⟩
    obtain ⟨Q, hQ, hQP⟩ := matrix_reindex ε n hP (projection_computes false)
    refine ⟨Q, hQ, fun p => ?_⟩
    change (p ∈ ⋃ k, F k) ↔ ∃ k, ¬ alternating n (matrixDomain ε Q) (Nat.pair 0 k) p
    simp only [Set.mem_iUnion]
    apply exists_congr
    intro k
    have hk := h k p
    have hq := hQP (Nat.pair 0 k) p
    simp only [Bool.false_eq_true, ite_false, Nat.unpair_pair] at hq
    simpa only [Set.mem_compl_iff, not_not] using
      (not_congr hk).trans (not_congr hq).symm

/-- Uniform families have genuine sections at the same parameter. -/
theorem UniformSigma.section {ε : ℕ → ℕ} {n : ℕ} {F : ℕ → Set (ℕ → ℕ)}
    (hF : UniformSigma ε n F) (k : ℕ) : Sigma ε n (F k) := by
  obtain ⟨P, hP, h⟩ := hF
  obtain ⟨Q, hQ, hQP⟩ := matrix_reindex ε n hP (numericalConstant_computes k)
  exact ⟨Q, hQ, fun p => (h k p).trans (hQP 0 p).symm⟩

theorem UniformPi.section {ε : ℕ → ℕ} {n : ℕ} {F : ℕ → Set (ℕ → ℕ)}
    (hF : UniformPi ε n F) (k : ℕ) : Pi ε n (F k) := UniformSigma.section hF k

/-- The discrete coordinate is the initial numerical input of the one matrix. -/
def SigmaNatBaire (ε : ℕ → ℕ) (n : ℕ) (P : Set (ℕ × (ℕ → ℕ))) : Prop :=
  UniformSigma ε n (fun k => {p | (k, p) ∈ P})

def PiNatBaire (ε : ℕ → ℕ) (n : ℕ) (P : Set (ℕ × (ℕ → ℕ))) : Prop :=
  SigmaNatBaire ε n Pᶜ

theorem sigma_succ_projection_iff (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) :
    Sigma ε (n + 1) A ↔ ∃ P : Set (ℕ × (ℕ → ℕ)), PiNatBaire ε n P ∧
      A = {p | ∃ k, (k, p) ∈ P} := by
  rw [sigma_succ_iff]
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨{z | z.2 ∈ F z.1}, hF, ?_⟩
    ext p
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  · rintro ⟨P, hP, rfl⟩
    refine ⟨fun k => {p | (k, p) ∈ P}, hP, ?_⟩
    ext p
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]

/-- The projective base projects an effectively closed set in the fixed
coordinatewise code for two Baire reals. Its complement has an actual closed
lambda semidecider. Each successor projects the complementary preceding
class, retaining the same parameter. No witness selection is asserted. -/
def ProjectiveSigma (ε : ℕ → ℕ) : ℕ → Set (ℕ → ℕ) → Prop
  | 0, A => ∃ C : Set (ℕ → ℕ), RelativelyEffectivelyClosed ε C ∧
      A = {p | ∃ q : ℕ → ℕ, pairBaire p q ∈ C}
  | n + 1, A => ∃ B : Set (ℕ → ℕ), ProjectiveSigma ε n B ∧
      A = {p | ∃ q : ℕ → ℕ, pairBaire p q ∉ B}

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lPi^1_n$, $\lSigma^1_{n+1}$: as in the boldface case but with the base level taken from the lightface side.
-/
def ProjectivePi (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  ProjectiveSigma ε n Aᶜ

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lDelta^k_n \;=\; \lSigma^k_n \cap \lPi^k_n$.
-/
def ProjectiveDelta (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  ProjectiveSigma ε n A ∧ ProjectivePi ε n A

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lSigma^1_1$: projections to $\BaireSpace$ of $\lPi^0_1$ (effectively closed) subsets of $\BaireSpace \times
        \BaireSpace$.
-/
theorem projectiveSigma_zero_iff (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    ProjectiveSigma ε 0 A ↔ ∃ C : Set (ℕ → ℕ), RelativelyEffectivelyClosed ε C ∧
      A = {p | ∃ q : ℕ → ℕ, pairBaire p q ∈ C} := Iff.rfl

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\lPi^1_n$, $\lSigma^1_{n+1}$: as in the boldface case but with the base level taken from the lightface side.
-/
theorem projectiveSigma_succ_iff (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) :
    ProjectiveSigma ε (n + 1) A ↔
      ∃ B : Set (ℕ → ℕ), ProjectivePi ε n B ∧ A = {p | ∃ q, pairBaire p q ∈ B} := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨Bᶜ, by simpa only [ProjectivePi, compl_compl] using hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    refine ⟨Bᶜ, hB, ?_⟩
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_not]

end LambdaFinite
end PolishSpaceBook
