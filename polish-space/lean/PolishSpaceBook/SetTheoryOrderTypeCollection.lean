module

public import PolishSpaceBook.SetTheoryOrdinalIsoFormulas

@[expose] public section

/-! # Collecting internally represented order types of subsets of a fixed set -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Input q codes (D,R); output α is its internally represented order type. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Use the internal ordinal-representation predicate $\iota$ from §{sec:internal-ordinal-representations} and define
    $$\tau(q,\alpha)\;:\equiv\;\exists D\,\exists R\,\exists g\,
     \bigl(q=\langle D,R\rangle\land\iota(D,R,\alpha,g)\bigr).$$
-/
def ordinalCodeFormula : ForcingFormulas.Formula 2 :=
  (orderedPairFormula (0 : Fin 5) 2 3 ⊓ reindex ordinalIsoFormula ![2, 3, 1, 4]).ex.ex.ex

def HasInternalOrderType (M q : ZFSet.{u}) (α : M) : Prop :=
  ∃ D R f : M, q = pair D.val R.val ∧ ordinalIsoFormula.Realize Empty.elim ![D, R, α, f]

lemma realize_ordinalCodeFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (q α : M) :
    ordinalCodeFormula.Realize Empty.elim ![q, α] ↔ HasInternalOrderType M q.val α := by
  have hp {n : ℕ} (q D R : Fin n) (xs : Fin n → M) :
      (orderedPairFormula q D R).Realize Empty.elim xs ↔ (xs q).val = pair (xs D).val (xs R).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q D R xs
  have hs (D R f : M) : (Fin.snoc (Fin.snoc (Fin.snoc ![q, α] D) R) f) ∘ ![2, 3, 1, 4] =
      ![D, R, α, f] := by
    funext i
    fin_cases i <;> rfl
  simp only [ordinalCodeFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, hp, hs]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    If two pairs of witnesses represent the same $q$, injectivity of ordered-pair coding makes their domains
    and relations equal. Uniqueness of ordinal representations then makes their ordinal targets equal.
    Thus each $q\in M$ has at most one internal target $\alpha$ satisfying $\tau(q,\alpha)$.
-/
lemma internalOrderType_unique {M q : ZFSet.{u}} (hM : M.IsTransitive) {α β : M}
    (hα : HasInternalOrderType M q α) (hβ : HasInternalOrderType M q β) : α = β := by
  obtain ⟨D, R, f, hq, hf⟩ := hα
  obtain ⟨E, S, g, hq', hg⟩ := hβ
  obtain ⟨hD, hR⟩ := ZFSet.pair_inj.mp (hq.symm.trans hq')
  have hDE : D = E := Subtype.ext hD
  have hRS : R = S := Subtype.ext hR
  subst E
  subst S
  exact (internal_ordinalIso_unique hM D R α β f g hf hg).1

lemma internalOrderType_isOrdinal {M q : ZFSet.{u}} (hM : M.IsTransitive) {α : M}
    (hα : HasInternalOrderType M q α) : α.val.IsOrdinal := by
  obtain ⟨D, R, f, _, hf⟩ := hα
  exact ((realize_ordinalIsoFormula hM D R α f).mp hf).1

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Products and internal power sets give
    $$C:=\InternalPowerSet{M}{W}\times\InternalPowerSet{M}{W\times W}\in M.$$
    Separation and Replacement now give
    $$\begin{aligned}
    B&:=\{q\in C:M\models\exists\alpha\,\tau(q,\alpha)\}\in M,\\
    T&:=\{\alpha_q:q\in B\}\in M,
    \end{aligned}$$
    where $\alpha_q$ is the unique internal ordinal specified by $\tau$.
    Every member of $T$ is an actual ordinal, by the recognition lemma for $\iota$.
    In particular, whenever $D,R,\alpha,g\in M$ satisfy
    $$D\IncludedIn W,\qquad R\IncludedIn W\times W,\qquad
     M\models\iota(D,R,\alpha,g),$$
    the code $\langle D,R\rangle$ belongs to $B$, so $\alpha\in T$.
    The construction uses only internal power sets and a single-valued defining formula; it assumes neither
    that every external subset belongs to $M$ nor that witnesses can be chosen uniformly in $M$.
-/
theorem internal_order_types_collection {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : M ⊨ replacementSentence ordinalCodeFormula) (W : M) :
    ∃ T : M, (∀ α ∈ T.val, α.IsOrdinal) ∧
      ∀ D R α f : M, D.val ⊆ W.val → R.val ⊆ ZFSet.prod W.val W.val →
        ordinalIsoFormula.Realize Empty.elim ![D, R, α, f] → α.val ∈ T.val := by
  classical
  let P := internalPowerSet M W.val
  let Q := internalPowerSet M (ZFSet.prod W.val W.val)
  have hP : P ∈ M := internalPowerSet_mem hM hpower W.property
  have hQ : Q ∈ M := internalPowerSet_mem hM hpower
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) W.property W.property)
  let C := ZFSet.prod P Q
  have hC : C ∈ M := prod_mem_of_separation hM hpair hunion hpower (hsep _) hP hQ
  let B := C.sep (fun q => ∃ α : M, HasInternalOrderType M q α)
  have hB : B ∈ M := by
    apply separation_mem_of_absolute hM ordinalCodeFormula.ex (hsep _) Fin.elim0 hC
      (fun q => ∃ α : M, HasInternalOrderType M q α)
    intro q _
    simp only [BoundedFormula.realize_ex]
    have hs (α : M) : Fin.snoc (Fin.snoc Fin.elim0 q) α = ![q, α] := by
      funext i
      fin_cases i <;> rfl
    simp only [hs, realize_ordinalCodeFormula hM]
  have hx (q : B) : ∃ α : M, HasInternalOrderType M q.val α := (ZFSet.mem_sep.mp q.property).2
  let t (q : B) : M := (hx q).choose
  have ht (q : B) : HasInternalOrderType M q.val (t q) := (hx q).choose_spec
  have hT : ZFSet.range (fun q : B => (t q).val) ∈ M := by
    apply replacement_image_mem hM ordinalCodeFormula hrep Fin.elim0 hB t
    intro q α
    have hs : Fin.snoc (Fin.snoc Fin.elim0 ⟨q.val, hM.mem_trans q.property hB⟩) α =
        ![⟨q.val, hM.mem_trans q.property hB⟩, α] := by
      funext i
      fin_cases i <;> rfl
    rw [hs, realize_ordinalCodeFormula hM]
    exact ⟨fun h => internalOrderType_unique hM h (ht q), fun h => h ▸ ht q⟩
  refine ⟨⟨_, hT⟩, ?_, ?_⟩
  · intro α hα
    obtain ⟨q, rfl⟩ := ZFSet.mem_range.mp hα
    exact internalOrderType_isOrdinal hM (ht q)
  · intro D R α f hDW hRW hf
    have hD : D.val ∈ P := ZFSet.mem_sep.mpr ⟨D.property, hDW⟩
    have hR : R.val ∈ Q := ZFSet.mem_sep.mpr ⟨R.property, hRW⟩
    have hqC : pair D.val R.val ∈ C := ZFSet.pair_mem_prod.mpr ⟨hD, hR⟩
    have htype : HasInternalOrderType M (pair D.val R.val) α := ⟨D, R, f, rfl, hf⟩
    let q : B := ⟨pair D.val R.val, ZFSet.mem_sep.mpr ⟨hqC, α, htype⟩⟩
    exact ZFSet.mem_range.mpr ⟨q, congrArg Subtype.val (internalOrderType_unique hM (ht q) htype)⟩

def ordinalUpperBound (T : ZFSet.{u}) : ZFSet.{u} := T ∪ ZFSet.sUnion T

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    This is a transitive set of ordinals. Indeed, a member of $T$ is an ordinal, and a member of $\bigcup T$
    is a member of such an ordinal. If $y\in H$ and $z\in y$, then either $y\in T$, which puts $z$ in $\bigcup T$,
    or $y\in\alpha\in T$, in which case transitivity of $\alpha$ again puts $z$ in $\bigcup T$.
    Thus $H$ is an ordinal.
-/
lemma ordinalUpperBound_isOrdinal {T : ZFSet.{u}} (hT : ∀ α ∈ T, α.IsOrdinal) :
    (ordinalUpperBound T).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro y hy z hz
    rcases ZFSet.mem_union.mp hy with hy | hy
    · exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨y, hy, hz⟩))
    · obtain ⟨α, hα, hyα⟩ := ZFSet.mem_sUnion.mp hy
      exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨α, hα, (hT α hα).mem_trans hz hyα⟩))
  · intro y hy
    rcases ZFSet.mem_union.mp hy with hy | hy
    · exact hT y hy
    · obtain ⟨α, hα, hyα⟩ := ZFSet.mem_sUnion.mp hy
      exact (hT α hα).mem hyα

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Put
    $$H:=T\cup\bigcup T\in M.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Also, every $\alpha\in T$ belongs to $H$, so $H$ strictly bounds all the represented
    types just collected.
-/
theorem internal_order_type_bound {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : M ⊨ replacementSentence ordinalCodeFormula) (W : M) :
    ∃ H : M, H.val.IsOrdinal ∧
      ∀ D R α f : M, D.val ⊆ W.val → R.val ⊆ ZFSet.prod W.val W.val →
        ordinalIsoFormula.Realize Empty.elim ![D, R, α, f] → α.val ∈ H.val := by
  obtain ⟨T, hT, hcover⟩ := internal_order_types_collection hM hpair hunion hpower hsep hrep W
  have hH : ordinalUpperBound T.val ∈ M :=
    binaryUnion_mem hM hpair hunion T.property (union_mem hM hunion T.property)
  exact ⟨⟨_, hH⟩, ordinalUpperBound_isOrdinal hT, fun D R α f hD hR hf =>
    ZFSet.mem_union.mpr (Or.inl (hcover D R α f hD hR hf))⟩

end PolishSpaceBook.SetTheoryModels
