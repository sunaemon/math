module

public import PolishSpaceBook.ForcingAtomicDefinability
public import PolishSpaceBook.ForcingCheckClosure

@[expose] public section

/-! # Removing the auxiliary bounds from the atomic forcing formulas -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-- Variables P,W,m,e,B; witnesses are the tag set and the two intermediate products. -/
def tableBoundFormula : ForcingFormulas.Formula 5 :=
  (unorderedPairFormula 5 2 3 ⊓ productEqFormula 1 1 6 ⊓ productEqFormula 0 6 7 ⊓
    productEqFormula 5 7 4).ex.ex.ex

lemma realize_unorderedPair_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (p a b : Fin n) (xs : Fin n → M) :
    (unorderedPairFormula p a b).Realize Empty.elim xs ↔ (xs p).val = ({(xs a).val, (xs b).val} : ZFSet.{u}) :=
  realize_unorderedPairFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) p a b xs

lemma realize_transitive_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (a : Fin n) (xs : Fin n → M) :
    (transitiveFormula a).Realize Empty.elim xs ↔ (xs a).val.IsTransitive :=
  realize_transitiveFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) a xs

lemma realize_tableBoundFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (xs : Fin 5 → M) : tableBoundFormula.Realize Empty.elim xs ↔
      (xs 4).val = tableBound (xs 0).val (xs 1).val (xs 2).val (xs 3).val := by
  simp only [tableBoundFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_unorderedPair_model hM, realize_productEqFormula hM hpair]
  dsimp [Fin.snoc, Fin.castPred, Fin.castLT]
  constructor
  · rintro ⟨tags, WW, PWW, ⟨⟨ht, hWW⟩, hPWW⟩, hB⟩
    rw [hB, ht, hPWW, hWW]
    rfl
  · intro hB
    let tags : M := ⟨{(xs 2).val, (xs 3).val}, unorderedPair_mem hM hpair (xs 2).property (xs 3).property⟩
    let WW : M := ⟨prod (xs 1).val (xs 1).val,
      prod_mem_of_separation hM hpair hunion hpower (hsep _) (xs 1).property (xs 1).property⟩
    let PWW : M := ⟨prod (xs 0).val WW.val,
      prod_mem_of_separation hM hpair hunion hpower (hsep _) (xs 0).property WW.property⟩
    exact ⟨tags, WW, PWW, ⟨⟨rfl, rfl⟩, rfl⟩, hB⟩

/-- Parameters P,R,p,σ,τ only. Tags, the transitive bound, its record bound, and the record are quantified. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Finally remove the auxiliary parameters from the definition. For $b\in\{0,1\}$, put $t_0:=m$ and $t_1:=e$,
    and define a fixed formula $\delta_b(P,R,p,\sigma,\tau)$ by
    $$\begin{aligned}
    \exists m\,\exists e\,\exists W\,\exists B\,\exists x\,\bigl[
    &m\ne e\land\mathrm{Trans}(W)\\
    &{}\land\sigma\in W\land\tau\in W\\
    &{}\land B=\{m,e\}\times(P\times(W\times W))\\
    &{}\land x=\ForcingTableEntry{t_b}{p}{\sigma}{\tau}\land\lambda_B(x)\bigr].
    \end{aligned}$$
    The parameters of $\lambda_B$ are $P,R,W,m,e,B$, all bound or displayed in this formula.
    The product equality has an explicit expansion using the tag set and the two intermediate products, followed by
    the product-equality formulas already verified. Thus $\delta_b$ is a formula of the pure membership language.
-/
def atomicForceFormula (b : Bool) : ForcingFormulas.Formula 5 :=
  ((equalAt 5 6).not ⊓ transitiveFormula 7 ⊓ memberAt 3 7 ⊓ memberAt 4 7 ⊓
    reindex tableBoundFormula ![0, 7, 5, 6, 8] ⊓
    tableEntryFormula 9 (if b then 6 else 5) 2 3 4 ⊓
    reindex boundedAtomicTableFormula ![0, 1, 7, 5, 6, 8, 9]).ex.ex.ex.ex.ex

lemma realize_atomicForceFormula_witnesses {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (b : Bool) (P R p σ τ : M) :
    (atomicForceFormula b).Realize Empty.elim ![P, R, p, σ, τ] ↔
      ∃ m e W B x : M, m ≠ e ∧ W.val.IsTransitive ∧ σ.val ∈ W.val ∧ τ.val ∈ W.val ∧
        B.val = tableBound P.val W.val m.val e.val ∧
        x.val = tableEntry (if b then e.val else m.val) p.val σ.val τ.val ∧
        boundedAtomicTableFormula.Realize Empty.elim ![P, R, W, m, e, B, x] := by
  cases b <;>
    simp only [atomicForceFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      BoundedFormula.realize_not, realize_equalAt_model, realize_memberAt_model, realize_transitive_model hM,
      realize_reindex, realize_tableBoundFormula hM hpair hunion hpower hsep,
      realize_tableEntryFormula hM hpair, and_assoc] <;>
    dsimp [Fin.snoc, Function.comp_def]
  all_goals
    apply exists_congr; intro m
    apply exists_congr; intro e
    apply exists_congr; intro W
    apply exists_congr; intro B
    apply exists_congr; intro x
    repeat' (apply and_congr_right; intro _)
    apply Iff.of_eq
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Atomic forcing is defined internally from P and its order relation, with no auxiliary bound parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For any witnesses to $\delta_b$, the agreement proposition identifies the asserted entry with the appropriate
    atomic forcing clause. Conversely, for $\sigma,\tau\in M$, Pairing gives $\{\sigma,\tau\}\in M$.
    The internal transitive-bound construction supplies a transitive $W\in M$ containing this pair as an element,
    hence containing both names. Choose $m=\emptyset$ and $e=\{\emptyset\}$; Infinity and Pairing put these distinct
    tags in $M$. The record bound and the required record belong to $M$, so agreement supplies all the witnesses.
    We have proved
    $$\begin{aligned}
    M\models\delta_0(P,R,p,\sigma,\tau)&\Longleftrightarrow p\forces^*\sigma\in\tau,\\
    M\models\delta_1(P,R,p,\sigma,\tau)&\Longleftrightarrow p\forces^*\sigma=\tau.
    \end{aligned}$$
    This requires the ground-model axioms used for internal transitive bounds, but no generic filter or Choice axiom.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The construction in §{sec:internal-atomic-forcing} produces its table in $M$ and supplies an explicit
    defining formula interpreted in $M$.
-/
theorem atomic_forcing_definable {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (P R : M) [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    (b : Bool) (σ τ : M) (p : Condition P.val) :
    (atomicForceFormula b).Realize Empty.elim
      ![P, R, ⟨p.val, hM.mem_trans p.property P.property⟩, σ, τ] ↔ p ∈ atomic P.val b σ.val τ.val := by
  rw [realize_atomicForceFormula_witnesses hM hpair hunion hpower hsep]
  constructor
  · rintro ⟨m, e, W, B, x, hme, hWt, hσ, hτ, hB, hx, hφ⟩
    have hme' : m.val ≠ e.val := fun h => hme (Subtype.ext h)
    exact (realize_boundedAtomicTableFormula P.val R.val hR hM hpair hunion hpower hsep
      P.property R.property W m e B x hB hme'
      (fun a ha c r hcr => child_mem_ground hWt ha hcr) b hσ hτ p hx).mp hφ
  · intro hp
    have hzero : (∅ : ZFSet.{u}) ∈ M := empty_mem_of_infinity hM hinf
    let m : M := ⟨∅, hzero⟩
    let e : M := ⟨{∅}, singleton_mem hM hpair hzero⟩
    have hme : m.val ≠ e.val := by
      intro h
      have h0 : (∅ : ZFSet.{u}) ∈ e.val := by change ∅ ∈ ({∅} : ZFSet.{u}); simp
      rw [← h] at h0
      exact ZFSet.notMem_empty _ h0
    let A : M := ⟨{σ.val, τ.val}, unorderedPair_mem hM hpair σ.property τ.property⟩
    obtain ⟨W', hWM, hAW, hWt⟩ := internal_transitive_bound hM hinf hpair hunion hpower hsep hrep A
    let W : M := ⟨W', hWM⟩
    have hσ : σ.val ∈ W.val := hWt.mem_trans (by change σ.val ∈ ({σ.val, τ.val} : ZFSet.{u}); simp) hAW
    have hτ : τ.val ∈ W.val := hWt.mem_trans (by change τ.val ∈ ({σ.val, τ.val} : ZFSet.{u}); simp) hAW
    let B : M := ⟨tableBound P.val W.val m.val e.val,
      tableBound_mem P.val hM hpair hunion hpower hsep P.property W.property m.property e.property⟩
    have hentry : tableEntry (if b then e.val else m.val) p.val σ.val τ.val ∈ B.val := by
      apply tableEntry_mem_bound.mpr
      refine ⟨?_, p.property, hσ, hτ⟩
      cases b <;> simp
    let x : M := ⟨_, hM.mem_trans hentry B.property⟩
    refine ⟨m, e, W, B, x, (fun h => hme (congrArg Subtype.val h)), hWt, hσ, hτ, rfl, rfl, ?_⟩
    exact (realize_boundedAtomicTableFormula P.val R.val hR hM hpair hunion hpower hsep
      P.property R.property W m e B x rfl hme
      (fun a ha c r hcr => child_mem_ground hWt ha hcr) b hσ hτ p rfl).mpr hp

end PolishSpaceBook.SetTheoryModels
