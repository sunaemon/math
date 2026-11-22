module

public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Projection and relative complement of entire internal sequences -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-- Parameters graph, range, component bound, input index, output; all witnesses are bounded. -/
def pairProjectionPredicate (left : Bool) : BoundedSetPredicate 5 :=
  .ex 1 (.ex 2 (.ex 2 (.conj (.pairMember 0 3 5)
    (.conj (.orderedPair 5 6 7) (.equal 4 (if left then 6 else 7))))))

lemma eval_pairProjectionPredicate (left : Bool) (W V : ℕ → ZFSet.{u}) (n : ℕ) (y : ZFSet.{u}) :
    let H := sequenceGraph (fun n => pair (W n) (V n))
    pairProjectionPredicate left |>.eval ![H, graphRange H, sUnion (sUnion (graphRange H)), natOrdinal n, y] ↔
      y = if left then W n else V n := by
  dsimp only
  let H := sequenceGraph (fun n => pair (W n) (V n))
  have hR : pair (W n) (V n) ∈ graphRange H :=
    mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph _ n _).mpr rfl⟩
  have hW := first_mem_doubleUnion hR
  have hV := second_mem_doubleUnion hR
  have he : (pairProjectionPredicate left).eval
      ![H, graphRange H, sUnion (sUnion (graphRange H)), natOrdinal n, y] ↔
      (∃ z ∈ graphRange H, ∃ w ∈ sUnion (sUnion (graphRange H)),
        ∃ v ∈ sUnion (sUnion (graphRange H)), pair (natOrdinal n) z ∈ H ∧
          z = pair w v ∧ y = if left then w else v) := by cases left <;> rfl
  rw [he]
  constructor
  · rintro ⟨z, _, w, _, v, _, hn, hz, hy⟩
    have he := (pair_mem_sequenceGraph _ n _).mp hn
    obtain ⟨hw, hv⟩ := ZFSet.pair_inj.mp (hz.symm.trans he)
    simpa only [hw, hv] using hy
  · intro hy
    exact ⟨pair (W n) (V n), hR, W n, hW, V n, hV,
      (pair_mem_sequenceGraph _ n _).mpr rfl, rfl, hy⟩

/-- Extract a whole component graph from a whole paired graph. -/
theorem pairSequence_projection_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (W V : ℕ → M) (hH : sequenceGraph (fun n => pair (W n).val (V n).val) ∈ M) (left : Bool) :
    sequenceGraph (fun n => if left then (W n).val else (V n).val) ∈ M := by
  let H : M := ⟨_, hH⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) H.property⟩
  let Q : M := ⟨sUnion (sUnion R.val), union_mem hM hunion (union_mem hM hunion R.property)⟩
  let values (n : ℕ) : M := if left then W n else V n
  have hvalues (n : ℕ) : (values n).val = if left then (W n).val else (V n).val := by
    cases left <;> rfl
  have hg := bounded_sequenceGraph_mem hM hinf hpair hsep hrep (pairProjectionPredicate left)
    ![H, R, Q] values (by
      intro n y
      have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![H, R, Q]) (natOrdinal n)) y.val =
          ![H.val, R.val, Q.val, natOrdinal n, y.val] := by funext i; fin_cases i <;> rfl
      rw [he, eval_pairProjectionPredicate, ← hvalues]
      exact Subtype.ext_iff.symm)
  simpa only [hvalues] using hg

/-- Parameters ambient set, removed set, resulting relative complement. -/
def relativeComplementPredicate : BoundedSetPredicate 3 :=
  .conj (.subset 2 0) (.all 0 (.iff (.member 3 2) (.neg (.member 3 1))))

lemma eval_relativeComplementPredicate (A W D : ZFSet.{u}) :
    relativeComplementPredicate.eval ![A, W, D] ↔ D = A.sep (fun x => x ∉ W) := by
  change (D ⊆ A ∧ ∀ x ∈ A, x ∈ D ↔ x ∉ W) ↔ _
  constructor
  · rintro ⟨hsub, h⟩
    ext x
    rw [ZFSet.mem_sep]
    exact ⟨fun hx => ⟨hsub hx, (h x (hsub hx)).mp hx⟩, fun hx => (h x hx.1).mpr hx.2⟩
  · rintro rfl
    exact ⟨fun _ hx => (ZFSet.mem_sep.mp hx).1, fun x hx => by simp [hx]⟩

/-- Parameters ambient set, input graph, its range, input index, output set. -/
def sequenceComplementPredicate : BoundedSetPredicate 5 :=
  .ex 2 (.conj (.pairMember 1 3 5) (relativeComplementPredicate.rename ![0, 5, 4]))

lemma eval_sequenceComplementPredicate (A : ZFSet.{u}) (W : ℕ → ZFSet.{u}) (n : ℕ) (D : ZFSet.{u}) :
    sequenceComplementPredicate.eval ![A, sequenceGraph W, graphRange (sequenceGraph W), natOrdinal n, D] ↔
      D = A.sep (fun x => x ∉ W n) := by
  simp only [sequenceComplementPredicate, eval, eval_rename, Fin.snoc]
  change (∃ w ∈ graphRange (sequenceGraph W), pair (natOrdinal n) w ∈ sequenceGraph W ∧
    relativeComplementPredicate.eval ![A, w, D]) ↔ _
  simp only [pair_mem_sequenceGraph, eval_relativeComplementPredicate]
  constructor
  · rintro ⟨w, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨W n, mem_graphRange.mpr ⟨natOrdinal n,
      (pair_mem_sequenceGraph W n _).mpr rfl⟩, rfl, h⟩

/-- Relative complement preserves the internality of the entire sequence, not just each value. -/
theorem sequenceRelativeComplement_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A : M) (W : ℕ → M) (hW : sequenceGraph (fun n => (W n).val) ∈ M) :
    sequenceGraph (fun n => A.val.sep (fun x => x ∉ (W n).val)) ∈ M := by
  let G : M := ⟨_, hW⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) G.property⟩
  have hD (n : ℕ) : A.val.sep (fun x => x ∉ (W n).val) ∈ M :=
    (BoundedSetPredicate.neg (.member (1 : Fin 2) 0)).separation_mem hM (hsep _) ![W n] A.property
  let values (n : ℕ) : M := ⟨_, hD n⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep sequenceComplementPredicate ![A, G, R] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![A, G, R]) (natOrdinal n)) y.val =
      ![A.val, G.val, R.val, natOrdinal n, y.val] := by funext i; fin_cases i <;> rfl
  rw [he, eval_sequenceComplementPredicate]
  constructor
  · intro he
    apply Subtype.ext
    exact he
  · intro he
    exact congrArg Subtype.val he

end PolishSpaceBook.SetTheoryModels
