module

public import PolishSpaceBook.ForcingTableFormulas

@[expose] public section


/-! # Internal construction and local definability of atomic forcing tables -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

variable (P R : ZFSet.{u}) [Preorder (Condition P)]
variable (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q)
include hR

lemma rawIncompatible_iff (q r : Condition P) :
    rawIncompatible P R q.val r.val ↔ incompatible P q r := by
  apply not_congr
  constructor
  · rintro ⟨s, hs, hsq, hsr⟩
    exact ⟨⟨s, hs⟩, (hR _ _).mp hsq, (hR _ _).mp hsr⟩
  · rintro ⟨s, hsq, hsr⟩
    exact ⟨s.val, s.property, (hR _ _).mpr hsq, (hR _ _).mpr hsr⟩

lemma rawMembershipStep_iff (W e T σ τ : ZFSet.{u}) (p : Condition P) :
    rawMembershipStep P R W e T p.val σ τ ↔ p ∈ membershipTableStep P W e T σ τ := by
  constructor
  · intro h q hqp
    obtain ⟨s, hs, hsq, π, hπ, r, hr, hπτ, hsr, he⟩ := h q.val q.property ((hR _ _).mpr hqp)
    exact ⟨⟨s, hs⟩, (hR _ _).mp hsq, π, hπ, ⟨r, hr⟩, hπτ, (hR _ _).mp hsr, he⟩
  · intro h q hq hqp
    obtain ⟨s, hsq, π, hπ, r, hπτ, hsr, he⟩ := h ⟨q, hq⟩ ((hR _ _).mp hqp)
    exact ⟨s.val, s.property, (hR _ _).mpr hsq, π, hπ, r.val, r.property, hπτ, (hR _ _).mpr hsr, he⟩

lemma rawEqualityHalfStep_iff (W m T σ τ : ZFSet.{u}) (p : Condition P) :
    rawEqualityHalfStep P R W m T p.val σ τ ↔ equalityHalfTableStep P W m T σ τ p := by
  constructor
  · intro h π hπ r hπσ q hqp
    obtain ⟨s, hs, hsq, halt⟩ := h π hπ r.val r.property hπσ q.val q.property ((hR _ _).mpr hqp)
    exact ⟨⟨s, hs⟩, (hR _ _).mp hsq, halt.imp_left ((rawIncompatible_iff P R hR ⟨s, hs⟩ r).mp)⟩
  · intro h π hπ r hr hπσ q hq hqp
    obtain ⟨s, hsq, halt⟩ := h π hπ ⟨r, hr⟩ hπσ ⟨q, hq⟩ ((hR _ _).mp hqp)
    exact ⟨s.val, s.property, (hR _ _).mpr hsq, halt.imp_left ((rawIncompatible_iff P R hR s ⟨r, hr⟩).mpr)⟩

lemma rawAtomicTableStep_iff (W m e T x : ZFSet.{u}) :
    rawAtomicTableStep P R W m e T x ↔ atomicTableStep P W m e T x := by
  constructor
  · rintro ⟨p, hp, σ, hσ, τ, hτ, h⟩
    refine ⟨⟨p, hp⟩, σ, hσ, τ, hτ, ?_⟩
    rcases h with ⟨he, hm⟩ | ⟨he, h1, h2⟩
    · exact Or.inl ⟨he, (rawMembershipStep_iff P R hR W e T σ τ ⟨p, hp⟩).mp hm⟩
    · exact Or.inr ⟨he, (rawEqualityHalfStep_iff P R hR W m T σ τ ⟨p, hp⟩).mp h1,
        (rawEqualityHalfStep_iff P R hR W m T τ σ ⟨p, hp⟩).mp h2⟩
  · rintro ⟨p, σ, hσ, τ, hτ, h⟩
    refine ⟨p.val, p.property, σ, hσ, τ, hτ, ?_⟩
    rcases h with ⟨he, hm⟩ | ⟨he, h1, h2⟩
    · exact Or.inl ⟨he, (rawMembershipStep_iff P R hR W e T σ τ p).mpr hm⟩
    · exact Or.inr ⟨he, (rawEqualityHalfStep_iff P R hR W m T σ τ p).mpr h1,
        (rawEqualityHalfStep_iff P R hR W m T τ σ p).mpr h2⟩

omit hR [Preorder (Condition P)] in
lemma tableBound_mem {M W m e : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hP : P ∈ M) (hW : W ∈ M) (hm : m ∈ M) (he : e ∈ M) : tableBound P W m e ∈ M := by
  have htags := insert_mem hM hpair hunion hm (singleton_mem hM hpair he)
  have hWW := prod_mem_of_separation hM hpair hunion hpower (hsep _) hW hW
  have hPWW := prod_mem_of_separation hM hpair hunion hpower (hsep _) hP hWW
  exact prod_mem_of_separation hM hpair hunion hpower (hsep _) htags hPWW

/-- This is one syntactic formula; the model is not a parameter. -/
def boundedAtomicTableFormula : ForcingFormulas.Formula 7 :=
  memberAt 6 5 ⊓ leastClosedMemberFormula atomicTableStepFormula

/-- The canonical intersection is an internal fixed table on every internal bound. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The internal fixed-point theorem therefore
    constructs $C\in M$ with $\Phi(C)=C$, defined by the formula $\lambda_B$ above.
-/
theorem internal_atomic_table {M W m e : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hP : P ∈ M) (hRM : R ∈ M) (hW : W ∈ M) (hm : m ∈ M) (he : e ∈ M) :
    let C := internalLeastClosed M (tableBound P W m e) (atomicTableStep P W m e)
    C ∈ M ∧ (tableBound P W m e).sep (atomicTableStep P W m e C) = C := by
  let ps : Fin 5 → M := ![⟨P, hP⟩, ⟨R, hRM⟩, ⟨W, hW⟩, ⟨m, hm⟩, ⟨e, he⟩]
  let B : M := ⟨tableBound P W m e, tableBound_mem P hM hpair hunion hpower hsep hP hW hm he⟩
  apply internal_definable_fixed_point hM hsep atomicTableStepFormula ps B (atomicTableStep P W m e)
  · intro T x _
    have hf := realize_atomicTableStepFormula hM hpair (Fin.snoc (Fin.snoc ps T) x)
    simpa [ps, Fin.snoc, Fin.castPred, Fin.castLT] using hf.trans (rawAtomicTableStep_iff P R hR W m e T.val x.val)
  · intro S T hST x _ hx
    exact atomicTableStep_mono P hST hx

/-- Consequently the actual external atomic truth table, on this domain, belongs to the model. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Agreement with the atomic recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The construction in §{sec:internal-atomic-forcing} produces its table in $M$ and supplies an explicit
    defining formula interpreted in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The rank-pair argument in §{sec:forcing-relation} constructs the atomic relations externally.
    We now give their internal definitions, using the internal least-fixed-point construction in
    §{sec:internal-model-fixed-points}. We show that the atomic recursion is the unique possible fixed table on each
    suitable bound.
-/
theorem exists_internal_atomic_table {M W m e : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hP : P ∈ M) (hRM : R ∈ M) (hWM : W ∈ M) (hm : m ∈ M) (he : e ∈ M) (hme : m ≠ e)
    (hW : ∀ τ ∈ W, ∀ σ (p : Condition P), pair σ p.val ∈ τ → σ ∈ W) :
    ∃ C ∈ M, C ⊆ tableBound P W m e ∧ ∀ (b : Bool) σ τ, σ ∈ W → τ ∈ W → ∀ p : Condition P,
      tableEntry (if b then e else m) p.val σ τ ∈ C ↔ p ∈ atomic P b σ τ := by
  obtain ⟨hC, hfix⟩ := internal_atomic_table P R hR hM hpair hunion hpower hsep hP hRM hWM hm he
  exact ⟨_, hC, internalLeastClosed_subset, fun b σ τ hσ hτ p => fixed_table_iff_atomic P hme hfix hW b σ τ hσ hτ p⟩

/-- The displayed least-closed-set formula defines each bounded atomic entry internally. -/
theorem realize_boundedAtomicTableFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hP : P ∈ M) (hRM : R ∈ M) (W m e B x : M)
    (hB : B.val = tableBound P W.val m.val e.val) (hme : m.val ≠ e.val)
    (hW : ∀ τ ∈ W.val, ∀ σ (p : Condition P), pair σ p.val ∈ τ → σ ∈ W.val)
    (b : Bool) {σ τ : ZFSet.{u}} (hσ : σ ∈ W.val) (hτ : τ ∈ W.val) (p : Condition P)
    (hx : x.val = tableEntry (if b then e.val else m.val) p.val σ τ) :
    boundedAtomicTableFormula.Realize Empty.elim ![⟨P, hP⟩, ⟨R, hRM⟩, W, m, e, B, x] ↔
      p ∈ atomic P b σ τ := by
  let ps : Fin 5 → M := ![⟨P, hP⟩, ⟨R, hRM⟩, W, m, e]
  have hφ (T y : M) (_hy : y.val ∈ B.val) :
      atomicTableStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ps T) y) ↔
        atomicTableStep P W.val m.val e.val T.val y.val := by
    have hf := realize_atomicTableStepFormula hM hpair (Fin.snoc (Fin.snoc ps T) y)
    simpa [ps, Fin.snoc, Fin.castPred, Fin.castLT] using hf.trans (rawAtomicTableStep_iff P R hR _ _ _ _ _)
  have hv := realize_leastClosedMember_step hM atomicTableStepFormula ps B x
    (atomicTableStep P W.val m.val e.val) hφ
  have hxs : ![⟨P, hP⟩, ⟨R, hRM⟩, W, m, e, B, x] = Fin.snoc (Fin.snoc ps B) x := by
    funext i
    fin_cases i <;> rfl
  have hmemb : boundedAtomicTableFormula.Realize Empty.elim ![⟨P, hP⟩, ⟨R, hRM⟩, W, m, e, B, x] ↔
      x.val ∈ internalLeastClosed M B.val (atomicTableStep P W.val m.val e.val) := by
    rw [hxs, boundedAtomicTableFormula, BoundedFormula.realize_inf, internalLeastClosed, ZFSet.mem_sep]
    change (x.val ∈ B.val ∧ _) ↔ _
    exact and_congr Iff.rfl hv
  obtain ⟨_, hfix⟩ := internal_atomic_table P R hR hM hpair hunion hpower hsep
    hP hRM W.property m.property e.property
  rw [hmemb, hB, hx]
  exact fixed_table_iff_atomic P hme hfix hW b σ τ hσ hτ p

end PolishSpaceBook.SetTheoryModels
