module

public import PolishSpaceBook.ForcingNameDefinability

@[expose] public section

/-! # Constructing the defining formula for each fixed forcing-language formula -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

def forcingAssignment {α : Type*} {n : ℕ} (xs : Fin n → α) (P R p : α) : Fin (n + 3) → α :=
  Fin.snoc (Fin.snoc (Fin.snoc xs P) R) p

/-- Replace the current condition with the newly quantified condition. -/
def conditionBinderIndex (n : ℕ) : Fin (n + 3) → Fin (n + 4) :=
  Fin.snoc (fun i => i.castSucc.castSucc) (Fin.last (n + 3))

/-- Move a quantified name before the three forcing parameters. -/
def nameBinderIndex (n : ℕ) : Fin (n + 4) → Fin (n + 4) :=
  Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc
    (fun i : Fin n => i.castSucc.castSucc.castSucc.castSucc) (Fin.last (n + 3)))
    (Fin.last n).castSucc.castSucc.castSucc) (Fin.last (n + 1)).castSucc.castSucc)
    (Fin.last (n + 2)).castSucc

lemma forcingAssignment_condition {α : Type*} {n : ℕ} (xs : Fin n → α) (P R p q : α) :
    (Fin.snoc (forcingAssignment xs P R p) q ∘ conditionBinderIndex n) = forcingAssignment xs P R q := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [forcingAssignment, conditionBinderIndex]

lemma forcingAssignment_name {α : Type*} {n : ℕ} (xs : Fin n → α) (P R p τ : α) :
    (Fin.snoc (forcingAssignment xs P R p) τ ∘ nameBinderIndex n) =
      forcingAssignment (Fin.snoc xs τ) P R p := by
  simp only [nameBinderIndex, forcingAssignment, Function.comp_def, apply_snoc,
    Fin.snoc_castSucc, Fin.snoc_last]

lemma forcingAssignment_name_test {α : Type*} {n : ℕ} (xs : Fin n → α) (P R p τ : α) :
    (Fin.snoc (forcingAssignment xs P R p) τ ∘
      ![(Fin.last n).castSucc.castSucc.castSucc, Fin.last (n + 3)]) = ![P, τ] := by
  funext i
  fin_cases i <;> simp [forcingAssignment]

/-- Its free variables are the original name tuple followed by P,R,p. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Use falsity, atomic formulas, implication, and universal quantification as primitives.
    Define the translation recursively, renaming bound variables to avoid capture:
    $$\begin{aligned}
    \rho_\bot(P,R,p,\vec\tau)&\;:\equiv\;\bot,\\
    \rho_{x_i\in x_j}(P,R,p,\vec\tau)
     &\;:\equiv\;\delta_0(P,R,p,\tau_i,\tau_j),\\
    \rho_{x_i=x_j}(P,R,p,\vec\tau)
     &\;:\equiv\;\delta_1(P,R,p,\tau_i,\tau_j),\\
    \rho_{\varphi\to\theta}(P,R,p,\vec\tau)
     &\;:\equiv\;\forall q\in P\;\bigl(\langle q,p\rangle\in R\\
     &\qquad\longrightarrow(\rho_\varphi(P,R,q,\vec\tau)\\
     &\qquad\qquad\longrightarrow\rho_\theta(P,R,q,\vec\tau))\bigr),\\
    \rho_{\forall x\,\varphi}(P,R,p,\vec\tau)
     &\;:\equiv\;\forall\sigma\;\bigl(\eta(P,\sigma)\\
     &\qquad\longrightarrow\rho_\varphi(P,R,p,\vec\tau,\sigma)\bigr).
    \end{aligned}$$
    The atomic formulas $\delta_0,\delta_1$ are those constructed in §{sec:internal-atomic-forcing}.
    Ordered-pair membership is expanded by its first-order definition, so every displayed clause is in the
    pure membership language and retains the parameters $P,R,p,\vec\tau$.
-/
def forcingTranslation : {n : ℕ} → ForcingFormulas.Formula n → ForcingFormulas.Formula (n + 3)
  | _, .falsum => .falsum
  | n, .equal s t => reindex (atomicForceFormula true)
      ![(Fin.last n).castSucc.castSucc, (Fin.last (n + 1)).castSucc, Fin.last (n + 2),
        (variableIndex s).castSucc.castSucc.castSucc, (variableIndex t).castSucc.castSucc.castSucc]
  | n, .rel .mem ts => reindex (atomicForceFormula false)
      ![(Fin.last n).castSucc.castSucc, (Fin.last (n + 1)).castSucc, Fin.last (n + 2),
        (variableIndex (ts 0)).castSucc.castSucc.castSucc, (variableIndex (ts 1)).castSucc.castSucc.castSucc]
  | n, .imp φ ψ => boundedAll (Fin.last n).castSucc.castSucc
      ((pairMemberFormula (Fin.last (n + 1)).castSucc.castSucc (Fin.last (n + 3))
        (Fin.last (n + 2)).castSucc).imp
        ((reindex (forcingTranslation φ) (conditionBinderIndex n)).imp
          (reindex (forcingTranslation ψ) (conditionBinderIndex n))))
  | n, .all φ => ((reindex nameFormula
        ![(Fin.last n).castSucc.castSucc.castSucc, Fin.last (n + 3)]).imp
      (reindex (forcingTranslation φ) (nameBinderIndex n))).all

lemma realize_forcingTranslation_imp {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (φ ψ : ForcingFormulas.Formula n) (xs : Fin n → M) (P R p : M) :
    (forcingTranslation (φ.imp ψ)).Realize Empty.elim (forcingAssignment xs P R p) ↔
      ∀ q : M, q.val ∈ P.val → pair q.val p.val ∈ R.val →
        (forcingTranslation φ).Realize Empty.elim (forcingAssignment xs P R q) →
        (forcingTranslation ψ).Realize Empty.elim (forcingAssignment xs P R q) := by
  simp only [forcingTranslation, realize_boundedAll_model, BoundedFormula.realize_imp,
    realize_pairMemberFormula_model hM, realize_reindex, forcingAssignment_condition]
  simp only [forcingAssignment, Fin.snoc_castSucc, Fin.snoc_last]

lemma realize_forcingTranslation_all {M : ZFSet.{u}} {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) (P R p : M) :
    (forcingTranslation φ.all).Realize Empty.elim (forcingAssignment xs P R p) ↔
      ∀ τ : M, nameFormula.Realize Empty.elim ![P, τ] →
        (forcingTranslation φ).Realize Empty.elim (forcingAssignment (Fin.snoc xs τ) P R p) := by
  simp only [forcingTranslation, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_reindex, forcingAssignment_name, forcingAssignment_name_test]

lemma forcingAssignment_atomic {α : Type*} {n : ℕ} (xs : Fin n → α) (P R p : α) (i j : Fin n) :
    (forcingAssignment xs P R p ∘
      ![(Fin.last n).castSucc.castSucc, (Fin.last (n + 1)).castSucc, Fin.last (n + 2),
        i.castSucc.castSucc.castSucc, j.castSucc.castSucc.castSucc]) = ![P, R, p, xs i, xs j] := by
  funext k
  fin_cases k <;> simp [forcingAssignment]

lemma termName_index (P M : ZFSet.{u}) {n : ℕ}
    (t : membershipLanguage.Term (Empty ⊕ Fin n)) (xs : Fin n → Name P M) :
    termName P M t xs = xs (variableIndex t) := by
  cases t with
  | var i => cases i with
    | inl e => exact e.elim
    | inr i => rfl
  | func f ts => exact f.elim

/-- Forgetting the name predicate retains the actual ground-model element. -/
def nameInModel {P M : ZFSet.{u}} (σ : Name P M) : M := ⟨σ.val, σ.property.1⟩

/-- Definability is a schema proved by induction on the fixed input formula. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Defining formulas for syntactic forcing
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Induct on the input formula. Falsity is immediate, and the atomic cases are the previously proved equivalences.
    For implication, transitivity ensures that the internal variables $q\in P$ run over all actual conditions;
    the test $\langle q,p\rangle\in R$ is precisely $q\le p$.
    The induction hypotheses therefore turn this clause into the defining implication clause of $\forces^*$.
    For universal quantification, the equivalence for $\eta$ identifies the domain with $M^P$.
    Apply the induction hypothesis to each extended tuple $\vec\tau,\sigma$ to obtain exactly the universal forcing
    clause. These steps prove the displayed equivalence in both directions.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The atomic definitions in §{sec:internal-atomic-forcing} extend to every fixed formula once the domain of
    name quantification is defined internally. Throughout this construction, let $M$ be transitive and satisfy
    Infinity, Pairing, Union, Power Set, Separation, and Replacement. Let $P,R\in M$, with $R$ coding the forcing order.
    No generic filter is needed for the construction.
-/
theorem forcing_definable {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (P R : M) [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) (p : Condition P.val) :
    (forcingTranslation φ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) P R ⟨p.val, hM.mem_trans p.property P.property⟩) ↔
      p ∈ force P.val M φ xs := by
  induction φ generalizing p with
  | falsum => rfl
  | equal s t =>
    rw [forcingTranslation, realize_reindex, forcingAssignment_atomic]
    simpa only [force, termName_index, nameInModel] using
      atomic_forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR true
        (nameInModel (xs (variableIndex s))) (nameInModel (xs (variableIndex t))) p
  | rel r ts =>
    cases r
    rw [forcingTranslation, realize_reindex, forcingAssignment_atomic]
    simpa only [force, termName_index, nameInModel] using
      atomic_forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR false
        (nameInModel (xs (variableIndex (ts 0)))) (nameInModel (xs (variableIndex (ts 1)))) p
  | imp φ ψ ihφ ihψ =>
    rw [realize_forcingTranslation_imp hM]
    change (∀ q : M, q.val ∈ P.val → pair q.val p.val ∈ R.val → _ → _) ↔
      ∀ q : Condition P.val, q ≤ p → q ∈ force P.val M φ xs → q ∈ force P.val M ψ xs
    constructor
    · intro h q hqp hφ
      let qM : M := ⟨q.val, hM.mem_trans q.property P.property⟩
      exact (ihψ xs q).mp (h qM q.property ((hR q p).mpr hqp) ((ihφ xs q).mpr hφ))
    · intro h q hq hqp hφ
      let qP : Condition P.val := ⟨q.val, hq⟩
      exact (ihψ xs qP).mpr (h qP ((hR qP p).mp hqp) ((ihφ xs qP).mp hφ))
  | all φ ih =>
    rw [realize_forcingTranslation_all]
    change (∀ τ : M, nameFormula.Realize Empty.elim ![P, τ] → _) ↔
      ∀ τ : Name P.val M, p ∈ force P.val M φ (Fin.snoc xs τ)
    constructor
    · intro h τ
      have hτ := (name_definable hM hinf hpair hunion hpower hsep hrep P (nameInModel τ)).mpr τ.property.2
      have hh := h (nameInModel τ) hτ
      have he : (nameInModel ∘ Fin.snoc xs τ) = Fin.snoc (fun i => nameInModel (xs i)) (nameInModel τ) :=
        apply_snoc nameInModel xs τ
      rw [← he] at hh
      exact (ih (Fin.snoc xs τ) p).mp hh
    · intro h τ hτ
      let τN : Name P.val M := ⟨τ.val, τ.property,
        (name_definable hM hinf hpair hunion hpower hsep hrep P τ).mp hτ⟩
      have hh := (ih (Fin.snoc xs τN) p).mpr (h τN)
      have he : (nameInModel ∘ Fin.snoc xs τN) = Fin.snoc (fun i => nameInModel (xs i)) τ :=
        apply_snoc nameInModel xs τN
      dsimp only [Function.comp_def] at he
      rw [he] at hh
      exact hh

/-- The actual set of conditions forcing a fixed formula with its name parameters. -/
def forcingSet (P M : ZFSet.{u}) [Preorder (Condition P)] {n : ℕ}
    (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P M) : ZFSet.{u} :=
  P.sep (fun p => ∃ hp : p ∈ P, (⟨p, hp⟩ : Condition P) ∈ force P M φ xs)

lemma mem_forcingSet (P M : ZFSet.{u}) [Preorder (Condition P)] {n : ℕ}
    (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P M) (p : Condition P) :
    p.val ∈ forcingSet P M φ xs ↔ p ∈ force P M φ xs := by
  simp [forcingSet, p.property]

/-- Separation applied to the constructed formula produces its actual forcing set internally. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: The forcing set belongs to the ground model
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Apply Separation in $M$ to $P$ using the formula $\rho_\varphi$ with parameters $P,R,\vec\tau$.
    Every element of $P$ lies in $M$, and the theorem identifies the separating predicate on each such element.
    Thus the internal separating set is exactly the displayed external set.
-/
theorem forcingSet_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (P R : M) [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) :
    forcingSet P.val M φ xs ∈ M := by
  apply separation_mem_of_absolute hM (forcingTranslation φ) (hsep _)
    (Fin.snoc (Fin.snoc (fun i => nameInModel (xs i)) P) R) P.property
  intro p hp
  have h := forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ xs ⟨p.val, hp⟩
  constructor
  · intro hφ
    exact ⟨hp, h.mp hφ⟩
  · rintro ⟨_, hφ⟩
    exact h.mpr hφ

end PolishSpaceBook.SetTheoryModels
