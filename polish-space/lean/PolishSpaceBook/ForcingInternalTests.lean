module

public import PolishSpaceBook.ForcingDefiningFormulas
public import PolishSpaceBook.ForcingFormulaTruth

@[expose] public section

/-! # Ground-model codes for the dense tests in the forcing truth proof -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-- Code a subset of the actual condition type as a set of its underlying sets. -/
def conditionSet (P : ZFSet.{u}) (A : Set (Condition P)) : ZFSet.{u} :=
  P.sep (fun p => ∃ hp : p ∈ P, (⟨p, hp⟩ : Condition P) ∈ A)

lemma mem_conditionSet (P : ZFSet.{u}) (A : Set (Condition P)) (p : Condition P) :
    p.val ∈ conditionSet P A ↔ p ∈ A := by
  simp [conditionSet, p.property]

lemma conditionSet_mem {M : ZFSet.{u}} (hM : M.IsTransitive) (P : M)
    (A : Set (Condition P.val)) {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hsep : M ⊨ separationSentence φ) (ps : Fin n → M)
    (hφ : ∀ p : Condition P.val, φ.Realize Empty.elim
      (Fin.snoc ps ⟨p.val, hM.mem_trans p.property P.property⟩) ↔ p ∈ A) :
    conditionSet P.val A ∈ M := by
  apply separation_mem_of_absolute hM φ hsep ps P.property
  intro p hp
  constructor
  · intro h
    exact ⟨hp, (hφ ⟨p.val, hp⟩).mp h⟩
  · rintro ⟨_, h⟩
    exact (hφ ⟨p.val, hp⟩).mpr h

/-- Five variables P,R,q,σ,τ; the extra variable replaces q by a stronger condition. -/
def conditionNegation5 (φ : ForcingFormulas.Formula 5) : ForcingFormulas.Formula 5 :=
  boundedAll 0 ((pairMemberFormula 1 5 2).imp (reindex φ ![0, 1, 5, 3, 4]).not)

lemma realize_conditionNegation5 {M : ZFSet.{u}} (hM : M.IsTransitive)
    (φ : ForcingFormulas.Formula 5) (P R q σ τ : M) :
    (conditionNegation5 φ).Realize Empty.elim ![P, R, q, σ, τ] ↔
      ∀ r : M, r.val ∈ P.val → pair r.val q.val ∈ R.val →
        ¬ φ.Realize Empty.elim ![P, R, r, σ, τ] := by
  simp only [conditionNegation5, realize_boundedAll_model, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, realize_pairMemberFormula_model hM, realize_reindex]
  have hx (r : M) : (Fin.snoc ![P, R, q, σ, τ] r ∘ ![0, 1, 5, 3, 4]) = ![P, R, r, σ, τ] := by
    funext i
    fin_cases i <;> rfl
  simp only [hx]
  rfl

/-- A witness for atomic membership, without taking its dense closure. -/
def membershipWitnessFormula : ForcingFormulas.Formula 5 :=
  (boundedExists 0 (pairMemberFormula 4 5 6 ⊓ pairMemberFormula 1 2 6 ⊓
    reindex (atomicForceFormula true) ![0, 1, 2, 3, 5])).ex

/-- A child witnessing one side of a failed equality. -/
def equalityDefectFormula : ForcingFormulas.Formula 5 :=
  (boundedExists 0 (pairMemberFormula 3 5 6 ⊓ pairMemberFormula 1 2 6 ⊓
    reindex (conditionNegation5 (atomicForceFormula false)) ![0, 1, 2, 5, 4])).ex

lemma realize_membershipWitnessFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (P R q σ τ : M) :
    membershipWitnessFormula.Realize Empty.elim ![P, R, q, σ, τ] ↔
      ∃ π r : M, r.val ∈ P.val ∧ pair π.val r.val ∈ τ.val ∧ pair q.val r.val ∈ R.val ∧
        (atomicForceFormula true).Realize Empty.elim ![P, R, q, σ, π] := by
  simp only [membershipWitnessFormula, BoundedFormula.realize_ex, realize_boundedExists_model,
    BoundedFormula.realize_inf, realize_pairMemberFormula_model hM, realize_reindex, and_assoc]
  dsimp [Fin.snoc, Function.comp_def]
  apply exists_congr
  intro π
  apply exists_congr
  intro r
  repeat' (apply and_congr_right; intro _)
  apply Iff.of_eq
  congr 1
  funext i
  fin_cases i <;> rfl

lemma realize_equalityDefectFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (P R q σ τ : M) :
    equalityDefectFormula.Realize Empty.elim ![P, R, q, σ, τ] ↔
      ∃ π r : M, r.val ∈ P.val ∧ pair π.val r.val ∈ σ.val ∧ pair q.val r.val ∈ R.val ∧
        (conditionNegation5 (atomicForceFormula false)).Realize Empty.elim ![P, R, q, π, τ] := by
  simp only [equalityDefectFormula, BoundedFormula.realize_ex, realize_boundedExists_model,
    BoundedFormula.realize_inf, realize_pairMemberFormula_model hM, realize_reindex, and_assoc]
  dsimp [Fin.snoc, Function.comp_def]
  apply exists_congr
  intro π
  apply exists_congr
  intro r
  repeat' (apply and_congr_right; intro _)
  apply Iff.of_eq
  congr 1
  funext i
  fin_cases i <;> rfl


def membershipTestFormula : ForcingFormulas.Formula 5 :=
  membershipWitnessFormula ⊔ conditionNegation5 membershipWitnessFormula

def equalityTestFormula : ForcingFormulas.Formula 5 :=
  (atomicForceFormula true ⊔ equalityDefectFormula) ⊔ reindex equalityDefectFormula ![0, 1, 2, 4, 3]

lemma conditionSet5_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R σ τ : M) (φ : ForcingFormulas.Formula 5) (A : Set (Condition P.val))
    (hφ : ∀ q : Condition P.val, φ.Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔ q ∈ A) :
    conditionSet P.val A ∈ M := by
  apply conditionSet_mem hM P A (reindex φ ![0, 1, 4, 2, 3]) (hsep _) ![P, R, σ, τ]
  intro q
  rw [realize_reindex]
  have he : (Fin.snoc ![P, R, σ, τ] ⟨q.val, hM.mem_trans q.property P.property⟩ ∘ ![0, 1, 4, 2, 3]) =
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact hφ q

def implicationTestFormula {n : ℕ} (φ ψ : ForcingFormulas.Formula n) : ForcingFormulas.Formula (n + 3) :=
  forcingTranslation (φ.imp ψ) ⊔ (forcingTranslation φ ⊓ forcingTranslation ψ.not)

/-- This is ordinary existential quantification over names, outside the forcing translation. -/
def existsNameForcingFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula (n + 3) :=
  ((reindex nameFormula ![(Fin.last n).castSucc.castSucc.castSucc, Fin.last (n + 3)]) ⊓
    reindex (forcingTranslation φ) (nameBinderIndex n)).ex

lemma realize_existsNameForcingFormula {M : ZFSet.{u}} {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) (P R p : M) :
    (existsNameForcingFormula φ).Realize Empty.elim (forcingAssignment xs P R p) ↔
      ∃ τ : M, nameFormula.Realize Empty.elim ![P, τ] ∧
        (forcingTranslation φ).Realize Empty.elim (forcingAssignment (Fin.snoc xs τ) P R p) := by
  simp only [existsNameForcingFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, forcingAssignment_name, forcingAssignment_name_test]

def universalTestFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula (n + 3) :=
  forcingTranslation φ.all ⊔ existsNameForcingFormula φ.not

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
include hR

lemma conditionNegation5_defines (φ : ForcingFormulas.Formula 5) (σ τ : M) (A : Set (Condition P.val))
    (hφ : ∀ q : Condition P.val, φ.Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔ q ∈ A) (q : Condition P.val) :
    (conditionNegation5 φ).Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔ q ∈ forcingNeg A := by
  rw [realize_conditionNegation5 hM]
  constructor
  · intro h r hrq hrA
    exact h ⟨r.val, hM.mem_trans r.property P.property⟩ r.property ((hR r q).mpr hrq) ((hφ r).mpr hrA)
  · intro h r hr hrq hφr
    exact h ⟨r.val, hr⟩ ((hR ⟨r.val, hr⟩ q).mp hrq) ((hφ ⟨r.val, hr⟩).mp hφr)

include hM hinf hpair hunion hpower hsep hrep

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The only additional witnesses in the atomic tests are pairs $\langle\pi,r\rangle$ belonging to a given name.
    The child-coordinate lemma in §{sec:forcing-names-valuation} puts $\pi$ in $M$, and transitivity puts $r\in P$
    in $M$. Hence their internal existential quantifiers lose no external witness.
-/
lemma membershipWitness_defines (σ τ : M) (q : Condition P.val) :
    membershipWitnessFormula.Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔ q ∈ membershipWitness P.val σ.val τ.val := by
  rw [realize_membershipWitnessFormula hM]
  constructor
  · rintro ⟨π, r, hr, hπ, hqr, hφ⟩
    exact ⟨π.val, ⟨r.val, hr⟩, hπ, (hR q ⟨r.val, hr⟩).mp hqr,
      (atomic_forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR true σ π q).mp hφ⟩
  · rintro ⟨π, r, hπ, hqr, hq⟩
    let πM : M := ⟨π, child_mem_ground hM τ.property hπ⟩
    exact ⟨πM, ⟨r.val, hM.mem_trans r.property P.property⟩, r.property, hπ, (hR q r).mpr hqr,
      (atomic_forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR true σ πM q).mpr hq⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Negating the existence of a
    stronger condition is also exact, since the condition set and its order code are internal.
-/
lemma equalityDefect_defines (σ τ : M) (q : Condition P.val) :
    equalityDefectFormula.Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔ q ∈ equalityDefect P.val σ.val τ.val := by
  rw [realize_equalityDefectFormula hM]
  have hn (π : M) := conditionNegation5_defines hM P R hR (atomicForceFormula false) π τ
    (atomic P.val false π.val τ.val)
    (atomic_forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR false π τ) q
  constructor
  · rintro ⟨π, r, hr, hπ, hqr, hφ⟩
    exact ⟨π.val, ⟨r.val, hr⟩, hπ, (hR q ⟨r.val, hr⟩).mp hqr, (hn π).mp hφ⟩
  · rintro ⟨π, r, hπ, hqr, hq⟩
    let πM : M := ⟨π, child_mem_ground hM σ.property hπ⟩
    exact ⟨πM, ⟨r.val, hM.mem_trans r.property P.property⟩, r.property, hπ, (hR q r).mpr hqr, (hn πM).mpr hq⟩


/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the defining-formula theorem of §{sec:internal-forcing-formulas}. In each test, replace a syntactic
    forcing assertion by its defining formula $\rho_\varphi(P,R,q,\vec\tau)$; in atomic assertions use
    $\delta_0$ or $\delta_1$. Expand order and pair membership by their verified first-order definitions.
    Condition quantifiers range over $P$, and quantification over names uses the internal predicate $\eta$.
    Transitivity and the defining-formula theorem identify these parts with the actual forcing clauses.
-/
lemma membershipTest_defines (σ τ : M) (q : Condition P.val) :
    membershipTestFormula.Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔
      q ∈ forcingDecision (membershipWitness P.val σ.val τ.val) := by
  rw [membershipTestFormula, BoundedFormula.realize_sup,
    membershipWitness_defines hM hinf hpair hunion hpower hsep hrep P R hR,
    conditionNegation5_defines hM P R hR membershipWitnessFormula σ τ _
      (membershipWitness_defines hM hinf hpair hunion hpower hsep hrep P R hR σ τ)]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the defining-formula theorem of §{sec:internal-forcing-formulas}. In each test, replace a syntactic
    forcing assertion by its defining formula $\rho_\varphi(P,R,q,\vec\tau)$; in atomic assertions use
    $\delta_0$ or $\delta_1$. Expand order and pair membership by their verified first-order definitions.
    Condition quantifiers range over $P$, and quantification over names uses the internal predicate $\eta$.
    Transitivity and the defining-formula theorem identify these parts with the actual forcing clauses.
-/
lemma equalityTest_defines (σ τ : M) (q : Condition P.val) :
    equalityTestFormula.Realize Empty.elim
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ↔ q ∈ equalityTest P.val σ.val τ.val := by
  simp only [equalityTestFormula, BoundedFormula.realize_sup, realize_reindex]
  have he : (![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, σ, τ] ∘ ![0, 1, 2, 4, 3]) =
      ![P, R, ⟨q.val, hM.mem_trans q.property P.property⟩, τ, σ] := by
    funext i
    fin_cases i <;> rfl
  rw [he, atomic_forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR,
    equalityDefect_defines hM hinf hpair hunion hpower hsep hrep P R hR,
    equalityDefect_defines hM hinf hpair hunion hpower hsep hrep P R hR]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Internal dense truth tests
-/
lemma membershipTest_mem (σ τ : M) :
    conditionSet P.val (forcingDecision (membershipWitness P.val σ.val τ.val)) ∈ M :=
  conditionSet5_mem hM hsep P R σ τ membershipTestFormula _
    (membershipTest_defines hM hinf hpair hunion hpower hsep hrep P R hR σ τ)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    All four test predicates are consequently first-order definitions with parameters in $M$. Separation on $P$
    puts their actual sets in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Internal dense truth tests
-/
lemma equalityTest_mem (σ τ : M) : conditionSet P.val (equalityTest P.val σ.val τ.val) ∈ M :=
  conditionSet5_mem hM hsep P R σ τ equalityTestFormula _
    (equalityTest_defines hM hinf hpair hunion hpower hsep hrep P R hR σ τ)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the defining-formula theorem of §{sec:internal-forcing-formulas}. In each test, replace a syntactic
    forcing assertion by its defining formula $\rho_\varphi(P,R,q,\vec\tau)$; in atomic assertions use
    $\delta_0$ or $\delta_1$. Expand order and pair membership by their verified first-order definitions.
    Condition quantifiers range over $P$, and quantification over names uses the internal predicate $\eta$.
    Transitivity and the defining-formula theorem identify these parts with the actual forcing clauses.
-/
lemma implicationTest_defines {n : ℕ} (φ ψ : ForcingFormulas.Formula n)
    (xs : Fin n → Name P.val M) (p : Condition P.val) :
    (implicationTestFormula φ ψ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) P R ⟨p.val, hM.mem_trans p.property P.property⟩) ↔
      p ∈ forcingImpTest (force P.val M φ xs) (force P.val M ψ xs) := by
  simp only [implicationTestFormula, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR, force]
  rfl

lemma existsNameForcing_defines {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P.val M) (p : Condition P.val) :
    (existsNameForcingFormula φ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) P R ⟨p.val, hM.mem_trans p.property P.property⟩) ↔
      ∃ τ : Name P.val M, p ∈ force P.val M φ (Fin.snoc xs τ) := by
  rw [realize_existsNameForcingFormula]
  constructor
  · rintro ⟨τ, hτ, hφ⟩
    let τN : Name P.val M := ⟨τ.val, τ.property,
      (name_definable hM hinf hpair hunion hpower hsep hrep P τ).mp hτ⟩
    have he : (nameInModel ∘ Fin.snoc xs τN) = Fin.snoc (fun i => nameInModel (xs i)) τ :=
      apply_snoc nameInModel xs τN
    dsimp only [Function.comp_def] at he
    rw [← he] at hφ
    exact ⟨τN, (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ (Fin.snoc xs τN) p).mp hφ⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨nameInModel τ, (name_definable hM hinf hpair hunion hpower hsep hrep P (nameInModel τ)).mpr
      τ.property.2, ?_⟩
    have hφ := (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ (Fin.snoc xs τ) p).mpr hτ
    have he := apply_snoc nameInModel xs τ
    rw [he] at hφ
    exact hφ

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For the universal test, its second alternative is expressed by
    $$\exists\sigma\,\bigl(\eta(P,\sigma)\land\rho_{\neg\varphi}(P,R,q,\vec\tau,\sigma)\bigr).$$
    Thus it quantifies over exactly the names in $M$; it does not require their collection as an internal set.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the defining-formula theorem of §{sec:internal-forcing-formulas}. In each test, replace a syntactic
    forcing assertion by its defining formula $\rho_\varphi(P,R,q,\vec\tau)$; in atomic assertions use
    $\delta_0$ or $\delta_1$. Expand order and pair membership by their verified first-order definitions.
    Condition quantifiers range over $P$, and quantification over names uses the internal predicate $\eta$.
    Transitivity and the defining-formula theorem identify these parts with the actual forcing clauses.
-/
lemma universalTest_defines {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P.val M) (p : Condition P.val) :
    (universalTestFormula φ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) P R ⟨p.val, hM.mem_trans p.property P.property⟩) ↔
      p ∈ forcingAllTest (fun τ => force P.val M φ (Fin.snoc xs τ)) := by
  simp only [universalTestFormula, BoundedFormula.realize_sup,
    forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR,
    existsNameForcing_defines hM hinf hpair hunion hpower hsep hrep P R hR,
    force, forcingAllTest, Set.mem_union, Set.mem_iUnion]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Internal dense truth tests
-/
lemma implicationTest_mem {n : ℕ} (φ ψ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) :
    conditionSet P.val (forcingImpTest (force P.val M φ xs) (force P.val M ψ xs)) ∈ M :=
  conditionSet_mem hM P _ (implicationTestFormula φ ψ) (hsep _)
    (Fin.snoc (Fin.snoc (fun i => nameInModel (xs i)) P) R)
    (implicationTest_defines hM hinf hpair hunion hpower hsep hrep P R hR φ ψ xs)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    All four test predicates are consequently first-order definitions with parameters in $M$. Separation on $P$
    puts their actual sets in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Internal dense truth tests
-/
lemma universalTest_mem {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → Name P.val M) :
    conditionSet P.val (forcingAllTest (fun τ => force P.val M φ (Fin.snoc xs τ))) ∈ M :=
  conditionSet_mem hM P _ (universalTestFormula φ) (hsep _)
    (Fin.snoc (Fin.snoc (fun i => nameInModel (xs i)) P) R)
    (universalTest_defines hM hinf hpair hunion hpower hsep hrep P R hR φ xs)

end Model
end PolishSpaceBook.SetTheoryModels
