module

public import PolishSpaceBook.ForcingAtomicTables
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # First-order formulas for the positive atomic table step -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

lemma forall_model_mem_iff {M : ZFSet.{u}} (hM : M.IsTransitive) (B : M) (Q : ZFSet.{u} → Prop) :
    (∀ y : M, y.val ∈ B.val → Q y.val) ↔ ∀ y ∈ B.val, Q y :=
  ⟨fun h y hy => h ⟨y, hM.mem_trans hy B.property⟩ hy, fun h y hy => h y.val hy⟩

lemma exists_model_mem_iff {M : ZFSet.{u}} (hM : M.IsTransitive) (B : M) (Q : ZFSet.{u} → Prop) :
    (∃ y : M, y.val ∈ B.val ∧ Q y.val) ↔ ∃ y ∈ B.val, Q y :=
  ⟨fun ⟨y, hy, hQ⟩ => ⟨y.val, hy, hQ⟩, fun ⟨y, hy, hQ⟩ => ⟨⟨y, hM.mem_trans hy B.property⟩, hy, hQ⟩⟩

lemma forall_internal_bound {M B : ZFSet.{u}} (hB : B ⊆ M) (Q : ZFSet.{u} → Prop) :
    (∀ y ∈ M, y ∈ B → Q y) ↔ ∀ y ∈ B, Q y :=
  ⟨fun h y hy => h y (hB hy) hy, fun h y _ hy => h y hy⟩

lemma realize_orderedPair_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (q a b : Fin n) (xs : Fin n → M) :
    (orderedPairFormula q a b).Realize Empty.elim xs ↔ (xs q).val = pair (xs a).val (xs b).val :=
  realize_orderedPairFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) q a b xs

/-- Explicit intermediate ordered pairs encode the four-field record. -/
def tableEntryFormula {n : ℕ} (x tag p σ τ : Fin n) : ForcingFormulas.Formula n :=
  (orderedPairFormula (Fin.last n).castSucc σ.castSucc.castSucc τ.castSucc.castSucc ⊓
    orderedPairFormula (Fin.last (n + 1)) p.castSucc.castSucc (Fin.last n).castSucc ⊓
    orderedPairFormula x.castSucc.castSucc tag.castSucc.castSucc (Fin.last (n + 1))).ex.ex

lemma realize_tableEntryFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (hpair : M ⊨ pairingSentence)
    {n : ℕ} (x tag p σ τ : Fin n) (xs : Fin n → M) :
    (tableEntryFormula x tag p σ τ).Realize Empty.elim xs ↔
      (xs x).val = tableEntry (xs tag).val (xs p).val (xs σ).val (xs τ).val := by
  simp only [tableEntryFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_orderedPair_model hM, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, hx⟩
    rw [hx, hb, ha]
    rfl
  · intro hx
    let a : M := ⟨pair (xs σ).val (xs τ).val, orderedPair_mem hM hpair (xs σ).property (xs τ).property⟩
    let b : M := ⟨pair (xs p).val a.val, orderedPair_mem hM hpair (xs p).property a.property⟩
    exact ⟨a, b, ⟨rfl, rfl⟩, hx⟩

def tableEntryMemberFormula {n : ℕ} (T tag p σ τ : Fin n) : ForcingFormulas.Formula n :=
  boundedExists T (tableEntryFormula (Fin.last n) tag.castSucc p.castSucc σ.castSucc τ.castSucc)

lemma realize_tableEntryMemberFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) {n : ℕ} (T tag p σ τ : Fin n) (xs : Fin n → M) :
    (tableEntryMemberFormula T tag p σ τ).Realize Empty.elim xs ↔
      tableEntry (xs tag).val (xs p).val (xs σ).val (xs τ).val ∈ (xs T).val := by
  simp only [tableEntryMemberFormula, realize_boundedExists_model, realize_tableEntryFormula hM hpair,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨x, hx, he⟩; exact he ▸ hx
  · intro hx
    exact ⟨⟨_, hM.mem_trans hx (xs T).property⟩, hx, rfl⟩

def incompatibilityPredicate {n : ℕ} (P R q r : Fin n) : BoundedSetPredicate n :=
  .neg (.ex P (.conj (.pairMember R.castSucc (Fin.last n) q.castSucc)
    (.pairMember R.castSucc (Fin.last n) r.castSucc)))

def incompatibilityFormula {n : ℕ} (P R q r : Fin n) : ForcingFormulas.Formula n :=
  (incompatibilityPredicate P R q r).compile

def rawIncompatible (P R q r : ZFSet.{u}) : Prop :=
  ¬ ∃ s ∈ P, pair s q ∈ R ∧ pair s r ∈ R

lemma realize_incompatibilityFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (P R q r : Fin n) (xs : Fin n → M) :
    (incompatibilityFormula P R q r).Realize Empty.elim xs ↔
      rawIncompatible (xs P).val (xs R).val (xs q).val (xs r).val := by
  simpa only [incompatibilityFormula, incompatibilityPredicate, BoundedSetPredicate.eval,
    Function.comp_def, Fin.snoc_last, Fin.snoc_castSucc, rawIncompatible] using
    (incompatibilityPredicate P R q r).realize_compile hM xs

/-- Variables are P, R, W, equality tag, T, p, σ, τ. -/
def membershipStepFormula : ForcingFormulas.Formula 8 :=
  boundedAll 0 ((pairMemberFormula 1 8 5).imp
    (boundedExists 0 (pairMemberFormula 1 9 8 ⊓ boundedExists 2 (boundedExists 0
      (pairMemberFormula 7 10 11 ⊓ pairMemberFormula 1 9 11 ⊓ tableEntryMemberFormula 4 3 9 6 10)))))

def rawMembershipStep (P R W e T p σ τ : ZFSet.{u}) : Prop :=
  ∀ q ∈ P, pair q p ∈ R → ∃ s ∈ P, pair s q ∈ R ∧ ∃ π ∈ W, ∃ r ∈ P,
    pair π r ∈ τ ∧ pair s r ∈ R ∧ tableEntry e s σ π ∈ T

lemma realize_membershipStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (xs : Fin 8 → M) :
    membershipStepFormula.Realize Empty.elim xs ↔ rawMembershipStep
      (xs 0).val (xs 1).val (xs 2).val (xs 3).val (xs 4).val (xs 5).val (xs 6).val (xs 7).val := by
  simp only [membershipStepFormula, realize_boundedAll_model, realize_boundedExists_model,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, realize_pairMemberFormula_model hM,
    realize_tableEntryMemberFormula hM hpair]
  have hP : (xs 0).val ⊆ M := hM.subset_of_mem (xs 0).property
  have hW : (xs 2).val ⊆ M := hM.subset_of_mem (xs 2).property
  simp only [Fin.snoc] -- Reduce the fixed variable assignments before eliminating model guards.
  simp [rawMembershipStep, forall_internal_bound hP, and_assoc]
  constructor
  · intro h q hq hqp
    obtain ⟨s, hs, hsq, _, π, hπ, _, r, hr, hπr, hsr, _, he⟩ := h q hq hqp
    exact ⟨s, hs, hsq, π, hπ, r, hr, hπr, hsr, he⟩
  · intro h q hq hqp
    obtain ⟨s, hs, hsq, π, hπ, r, hr, hπr, hsr, he⟩ := h q hq hqp
    exact ⟨s, hs, hsq, hP hs, π, hπ, hW hπ, r, hr, hπr, hsr, hP hr, he⟩

/-- Variables are P, R, W, membership tag, T, p, σ, τ. -/
def equalityHalfStepFormula : ForcingFormulas.Formula 8 :=
  boundedAll 2 (boundedAll 0 ((pairMemberFormula 6 8 9).imp
    (boundedAll 0 ((pairMemberFormula 1 10 5).imp (boundedExists 0
      (pairMemberFormula 1 11 10 ⊓
        (incompatibilityFormula 0 1 11 9 ⊔ tableEntryMemberFormula 4 3 11 8 7)))))))

def rawEqualityHalfStep (P R W m T p σ τ : ZFSet.{u}) : Prop :=
  ∀ π ∈ W, ∀ r ∈ P, pair π r ∈ σ → ∀ q ∈ P, pair q p ∈ R →
    ∃ s ∈ P, pair s q ∈ R ∧ (rawIncompatible P R s r ∨ tableEntry m s π τ ∈ T)

lemma realize_equalityHalfStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (xs : Fin 8 → M) :
    equalityHalfStepFormula.Realize Empty.elim xs ↔ rawEqualityHalfStep
      (xs 0).val (xs 1).val (xs 2).val (xs 3).val (xs 4).val (xs 5).val (xs 6).val (xs 7).val := by
  simp only [equalityHalfStepFormula, realize_boundedAll_model, realize_boundedExists_model,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    realize_pairMemberFormula_model hM, realize_tableEntryMemberFormula hM hpair,
    realize_incompatibilityFormula hM]
  have hP : (xs 0).val ⊆ M := hM.subset_of_mem (xs 0).property
  have hW : (xs 2).val ⊆ M := hM.subset_of_mem (xs 2).property
  simp [Fin.snoc, rawEqualityHalfStep, forall_internal_bound hP, forall_internal_bound hW]
  constructor
  · intro h π hπ r hr hπr q hq hqp
    obtain ⟨s, hs, hsq, _, halt⟩ := h π hπ r hr hπr q hq hqp
    exact ⟨s, hs, hsq, halt⟩
  · intro h π hπ r hr hπr q hq hqp
    obtain ⟨s, hs, hsq, halt⟩ := h π hπ r hr hπr q hq hqp
    exact ⟨s, hs, hsq, hP hs, halt⟩

/-- Parameters P,R,W,m,e followed by the candidate T and tested record x. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Here is an explicit first-order definition of the step:
    $$\begin{aligned}
    \varphi(T,x)\;:\equiv\;&\exists p\in P\;\exists\sigma\in W\;\exists\tau\in W\\
    &\bigl[(x=\ForcingTableEntry{m}{p}{\sigma}{\tau}\land A_T(p,\sigma,\tau))\\
    &\quad\lor(x=\ForcingTableEntry{e}{p}{\sigma}{\tau}\land E_T(p,\sigma,\tau)\\
    &\qquad\land E_T(p,\tau,\sigma))\bigr].
    \end{aligned}$$
    Expand $q\le p$ as $\langle q,p\rangle\in R$, and expand incompatibility as
    $$s\perp r\quad\Longleftrightarrow\quad
     \neg\exists t\in P\,(\langle t,s\rangle\in R\land\langle t,r\rangle\in R).$$
    For each record equality introduce the two intermediate pairs
    $$u=\langle\sigma,\tau\rangle,\qquad
    v=\langle p,u\rangle,\qquad x=\langle b,v\rangle,$$
    and use the previously verified formulas for ordered pairs and pair membership.
-/
def atomicTableStepFormula : ForcingFormulas.Formula 7 :=
  boundedExists 0 (boundedExists 2 (boundedExists 2
    ((tableEntryFormula 6 3 7 8 9 ⊓ reindex membershipStepFormula ![0, 1, 2, 4, 5, 7, 8, 9]) ⊔
     (tableEntryFormula 6 4 7 8 9 ⊓ reindex equalityHalfStepFormula ![0, 1, 2, 3, 5, 7, 8, 9] ⊓
       reindex equalityHalfStepFormula ![0, 1, 2, 3, 5, 7, 9, 8]))))

def rawAtomicTableStep (P R W m e T x : ZFSet.{u}) : Prop :=
  ∃ p ∈ P, ∃ σ ∈ W, ∃ τ ∈ W,
    (x = tableEntry m p σ τ ∧ rawMembershipStep P R W e T p σ τ) ∨
    (x = tableEntry e p σ τ ∧ rawEqualityHalfStep P R W m T p σ τ ∧
      rawEqualityHalfStep P R W m T p τ σ)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Pairing puts the intermediate pairs in the model. All remaining quantifiers range over $P$, $W$, or the candidate
    table, so transitivity gives exactly the external step predicate.
-/
lemma realize_atomicTableStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (xs : Fin 7 → M) :
    atomicTableStepFormula.Realize Empty.elim xs ↔ rawAtomicTableStep
      (xs 0).val (xs 1).val (xs 2).val (xs 3).val (xs 4).val (xs 5).val (xs 6).val := by
  simp only [atomicTableStepFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, realize_tableEntryFormula hM hpair, realize_reindex,
    realize_membershipStepFormula hM hpair, realize_equalityHalfStepFormula hM hpair]
  have hP : (xs 0).val ⊆ M := hM.subset_of_mem (xs 0).property
  have hW : (xs 2).val ⊆ M := hM.subset_of_mem (xs 2).property
  simp [Fin.snoc, rawAtomicTableStep, and_assoc]
  constructor
  · rintro ⟨p, hp, _, σ, hσ, _, τ, hτ, _, h⟩
    exact ⟨p, hp, σ, hσ, τ, hτ, h⟩
  · rintro ⟨p, hp, σ, hσ, τ, hτ, h⟩
    exact ⟨p, hp, hP hp, σ, hσ, hW hσ, τ, hτ, hW hτ, h⟩

end PolishSpaceBook.SetTheoryModels
