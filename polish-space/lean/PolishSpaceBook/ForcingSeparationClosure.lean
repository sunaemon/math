module

public import PolishSpaceBook.ForcingSeparationNames
public import PolishSpaceBook.ForcingGenericTruth

@[expose] public section

/-! # Internal construction of separation names and the full Separation schema in generic extensions -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

def separationParams {α : Type*} {n : ℕ} (xs : Fin n → α) (τ P R A : α) : Fin (n + 4) → α :=
  Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs τ) P) R) A

/-- In the child clause, append σ to the name parameters and use q as the forcing condition. -/
def separationForcingIndex (n : ℕ) : Fin (n + 4) → Fin (n + 8) :=
  forcingAssignment
    (Fin.snoc (fun i : Fin n => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 5)).castSucc.castSucc)
    (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (n + 2)).castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (n + 6)).castSucc

lemma separation_reindex {α : Type*} {n : ℕ} (xs : Fin n → α) (τ P R A z σ q r : α) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (separationParams xs τ P R A) z) σ) q) r ∘
      separationForcingIndex n) = forcingAssignment (Fin.snoc xs σ) P R q := by
  simp only [separationForcingIndex, forcingAssignment, separationParams, Function.comp_def,
    apply_snoc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The free variables are the old name tuple, τ,P,R,A,z; σ,q,r are bounded witnesses. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    To put this specified name in the model, use the actual defining formula from §{sec:internal-forcing-formulas}:
    $$\begin{aligned}
    &\chi(z)\;:\equiv\;\exists\sigma\in A\;\exists q\in P\;\exists r\in P\,
     \bigl[z=\langle\sigma,q\rangle\\
    &\qquad{}\land\langle\sigma,r\rangle\in\tau\land\langle q,r\rangle\in R\\
    &\qquad{}\land\rho_\varphi(P,R,q,\vec\nu,\sigma)\bigr].
    \end{aligned}$$
    Its parameters are the finite tuple $\vec\nu$ and the sets $\tau,P,R,A$, all in $M$.
-/
def separationClosureFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula (n + 5) :=
  boundedExists (Fin.last (n + 3)).castSucc
    (boundedExists (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
      (boundedExists (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc.castSucc
        (orderedPairFormula (Fin.last (n + 4)).castSucc.castSucc.castSucc
            (Fin.last (n + 5)).castSucc.castSucc (Fin.last (n + 6)).castSucc ⊓
          pairMemberFormula (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
            (Fin.last (n + 5)).castSucc.castSucc (Fin.last (n + 7)) ⊓
          pairMemberFormula (Fin.last (n + 2)).castSucc.castSucc.castSucc.castSucc.castSucc
            (Fin.last (n + 6)).castSucc (Fin.last (n + 7)) ⊓
          reindex (forcingTranslation φ) (separationForcingIndex n))))

lemma realize_separationClosureFormula {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) (τ P R A z : M) :
    (separationClosureFormula φ).Realize Empty.elim (Fin.snoc (separationParams xs τ P R A) z) ↔
      ∃ σ : M, σ.val ∈ A.val ∧ ∃ q : M, q.val ∈ P.val ∧ ∃ r : M, r.val ∈ P.val ∧
        z.val = pair σ.val q.val ∧ pair σ.val r.val ∈ τ.val ∧ pair q.val r.val ∈ R.val ∧
          (forcingTranslation φ).Realize Empty.elim (forcingAssignment (Fin.snoc xs σ) P R q) := by
  simp only [separationClosureFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
    realize_orderedPair_model hM, realize_pairMemberFormula_model hM, realize_reindex, separation_reindex,
    and_assoc]
  simp only [separationParams, Fin.snoc_castSucc, Fin.snoc_last]

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
include hM hinf hpair hunion hpower hsep hrep hR

/-- A single internally defining formula separates the name from a product in the ground model. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Whenever the pair-membership conjunct holds, the child-coordinate lemma puts $\sigma$ in the model and the name
    property of $\tau$ makes it a name. Thus the defining-formula theorem applies to the entire extended tuple.
    Transitivity identifies the bounded witnesses with the actual elements of their bounds, and the ordered-pair
    formulas have their actual meanings. Consequently the internal interpretation of $\chi$ is exactly the predicate
    used to define $\theta$. Separation in $M$ gives $\theta\in M$.
    The defining formula need not be bounded, so this step uses the full Separation schema.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Put $A:=\bigcup\bigcup\tau$, so every first-coordinate name occurring in $\tau$ belongs to $A$.
    Union and the internal product construction give $A\times P\in M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The defining formulas and the truth theorem now let us build names for definable subsets.
    The construction is uniform in the finite tuple of name parameters and does not depend on the generic filter.
-/
theorem separationName_mem_ground {n : ℕ} (τ : Name P.val M)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → Name P.val M) :
    separationName P.val M τ φ xs ∈ M := by
  have hA : childBound τ.val ∈ M := union_mem hM hunion (union_mem hM hunion τ.property.1)
  have hB := prod_mem_of_separation hM hpair hunion hpower (hsep _) hA P.property
  let A : M := ⟨childBound τ.val, hA⟩
  apply separation_mem_of_absolute hM (separationClosureFormula φ) (hsep _)
    (separationParams (fun i => nameInModel (xs i)) (nameInModel τ) P R A) hB
  intro z _
  rw [realize_separationClosureFormula hM]
  constructor
  · rintro ⟨σ, _, q, hq, r, hr, he, hπ, hqr, hφ⟩
    let σN : Name P.val M := ⟨σ.val, σ.property, τ.property.2.child hπ⟩
    let qc : Condition P.val := ⟨q.val, hq⟩
    let rc : Condition P.val := ⟨r.val, hr⟩
    have heq : (nameInModel ∘ Fin.snoc xs σN) = Fin.snoc (fun i => nameInModel (xs i)) σ :=
      apply_snoc nameInModel xs σN
    dsimp only [Function.comp_def] at heq
    rw [← heq] at hφ
    exact ⟨σN, qc, rc, he, hπ, (hR qc rc).mp hqr,
      (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ (Fin.snoc xs σN) qc).mp hφ⟩
  · rintro ⟨σ, q, r, he, hπ, hqr, hφ⟩
    have ht := (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ (Fin.snoc xs σ) q).mpr hφ
    rw [apply_snoc] at ht
    exact ⟨nameInModel σ, child_mem_doubleUnion hπ,
      ⟨q.val, hM.mem_trans q.property P.property⟩, q.property,
      ⟨r.val, hM.mem_trans r.property P.property⟩, r.property, he, hπ, (hR q r).mpr hqr, ht⟩

/-- Every Separation instance holds on the actual domain of a generic extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Finally, $\theta\in M^P$ puts $y:=\theta^G$ in $M[G]$.
    For every $z\in M[G]$, the valuation identity gives
    $$z\in y\quad\Longleftrightarrow\quad z\in x\ \land\ M[G]\models\varphi(\vec a,z).$$
    This is precisely the internal Separation instance for the original formula and parameters.
    Every finite tuple of extension parameters has a tuple of ground-model names by the definition of the extension,
    so the argument proves the whole schema.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Fix a formula $\varphi(\vec a,z)$, a set $x\in M[G]$, and a finite tuple $\vec a$ of parameters from $M[G]$.
    Choose names $\tau,\vec\nu\in M^P$ with $x=\tau^G$ and $\vec a=\vec\nu^G$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Separation in generic extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The construction in §{sec:generic-separation} proves the full Separation schema using the truth theorem.
-/
theorem extension_models_separation (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) : Extension P.val M G ⊨ separationSentence φ := by
  classical
  apply (realize_separation (Extension P.val M G) φ).mpr
  intro ps x
  choose xs hxs using fun i => evalName_surjective P.val M G (ps i)
  obtain ⟨τ, hτ⟩ := evalName_surjective P.val M G x
  let ρ : Name P.val M := ⟨separationName P.val M τ φ xs,
    separationName_mem_ground hM hinf hpair hunion hpower hsep hrep P R hR τ φ xs,
    separationName_isName P.val M τ φ xs⟩
  refine ⟨evalName P.val M G ρ, ?_⟩
  intro z
  change z.val ∈ value P.val G (separationName P.val M τ φ xs) ↔
    z.val ∈ x.val ∧ φ.Realize Empty.elim (Fin.snoc ps z)
  rw [mem_value_separationName P.val M hM τ φ xs G
    (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG) z]
  have hps : (fun i => evalName P.val M G (xs i)) = ps := funext hxs
  have hx : value P.val G τ.val = x.val := congrArg Subtype.val hτ
  rw [hps, hx]

end Model
end PolishSpaceBook.SetTheoryModels
