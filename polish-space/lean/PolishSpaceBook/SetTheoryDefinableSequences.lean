module

public import PolishSpaceBook.SetTheoryCountableChoice
public import PolishSpaceBook.SetTheoryPredicateReflection
public import PolishSpaceBook.SetTheoryNaturalPowers

@[expose] public section

/-! # Entire sequence graphs from bounded value definitions -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-- Reindexing by natural ordinals preserves the graph collected by Replacement. -/
theorem definable_sequenceGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)) (ps : Fin k → M) (s : ℕ → M)
    (heval : ∀ n (N y : M), N.val = natOrdinal n →
      (φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps N) y) ↔ y = s n)) :
    sequenceGraph (fun n => (s n).val) ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  let e : ℕ ≃ (Ordinal.omega0.toZFSet : ZFSet.{u}) :=
    Equiv.ofBijective (fun n => ⟨natOrdinal n, mem_omegaOrdinal.mpr ⟨n, rfl⟩⟩)
      ⟨fun _ _ h => natOrdinal_injective (congrArg Subtype.val h), fun a => by
        obtain ⟨n, hn⟩ := mem_omegaOrdinal.mp a.property
        exact ⟨n, Subtype.ext hn⟩⟩
  let f (a : (Ordinal.omega0.toZFSet : ZFSet.{u})) : M := s (e.symm a)
  have hgraph := replacement_graph_mem hM hpair φ (hrep _) ps hΩ f (by
    intro a y
    have ha : natOrdinal (e.symm a) = a.val :=
      congrArg Subtype.val (e.apply_symm_apply a)
    exact heval _ _ y ha.symm)
  have he : functionGraph (fun a => (f a).val) = sequenceGraph (fun n => (s n).val) := by
    ext q
    simp only [functionGraph, sequenceGraph, ZFSet.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e.symm a, by rw [show natOrdinal (e.symm a) = a.val from
        congrArg Subtype.val (e.apply_symm_apply a)]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨e n, by simp only [f, Equiv.symm_apply_apply]; rfl⟩
  rwa [he] at hgraph

/-- Bounded definitions use the shared interpretation theorem before graph collection. -/
theorem bounded_sequenceGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {k : ℕ} (p : BoundedSetPredicate (k + 2)) (ps : Fin k → M) (s : ℕ → M)
    (heval : ∀ n, ∀ y : M,
      p.eval (Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val) ↔ y = s n) :
    sequenceGraph (fun n => (s n).val) ∈ M := by
  apply definable_sequenceGraph_mem hM hinf hpair hsep hrep p.compile ps s
  intro n N y hN
  rw [p.realize_compile hM]
  simp only [Fin.comp_snoc, hN]
  exact heval n y

/-- Choose witnesses to a bounded relation while preserving the whole internal sequence graph. -/
theorem bounded_countable_choice {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) {k : ℕ} (p : BoundedSetPredicate (k + 2)) (ps : Fin k → M)
    (htotal : ∀ n : ℕ, ∃ y : M,
      p.eval (Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val)) :
    ∃ s : ℕ → M, sequenceGraph (fun n => (s n).val) ∈ M ∧ ∀ n,
      p.eval (Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) (s n).val) := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  obtain ⟨s, hs, hp⟩ := internal_countable_choice hM hinf hpair hunion hpower hsep hrep hchoice
    p.compile ps Ω rfl (by
      intro N hN
      obtain ⟨n, hn⟩ := mem_omegaOrdinal.mp hN
      obtain ⟨y, hy⟩ := htotal n
      refine ⟨y, (p.realize_compile hM _).mpr ?_⟩
      simpa only [Fin.comp_snoc, ← hn] using hy)
  refine ⟨s, hs, fun n => ?_⟩
  let N : M := ⟨natOrdinal n, hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property⟩
  simpa only [Fin.comp_snoc] using (p.realize_compile hM _).mp (hp N n rfl)

lemma constantSequenceGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (a : M) : sequenceGraph (fun _ => a.val) ∈ M := by
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep (.equal 2 0) ![a] (fun _ => a)
  intro n y
  constructor
  · intro he
    apply Subtype.ext
    exact he
  · intro he
    exact congrArg Subtype.val he

/-- Parameters omega, addition graph, power graph, offset, input, output. -/
def shiftedPowerPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.conj (binaryMemberAt 1 3 4 6) (.pairMember 2 6 5))

lemma eval_shiftedPowerPredicate (k n : ℕ) (y : ZFSet.{u}) :
    shiftedPowerPredicate.eval ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a + b),
      sequenceGraph (fun j => natOrdinal (2 ^ j)), natOrdinal k, natOrdinal n, y] ↔
      y = natOrdinal (2 ^ (k + n)) := by
  simp [shiftedPowerPredicate, eval, eval_binaryMemberAt, Fin.snoc, Fin.castPred, Fin.castLT, exists_mem_omegaOrdinal,
    pair_mem_naturalBinaryGraph, pair_mem_sequenceGraph, natOrdinal_injective.eq_iff]

/-- The whole sequence of dyadic denominators is internal, for every fixed natural offset. -/
theorem shiftedTwoPowerGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (k : ℕ) : sequenceGraph (fun n => natOrdinal (2 ^ (k + n))) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let A : M := ⟨_, naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩
  let P : M := ⟨_, naturalTwoPowerGraph_mem hM hinf hpair hunion hpower hsep⟩
  let K : M := ⟨natOrdinal k, hn k⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep shiftedPowerPredicate ![Ω, A, P, K]
    (fun n => ⟨natOrdinal (2 ^ (k + n)), hn _⟩)
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![Ω, A, P, K]) (natOrdinal n)) y.val =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a + b),
        sequenceGraph (fun j => natOrdinal (2 ^ j)), natOrdinal k, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_shiftedPowerPredicate]
  constructor
  · intro he
    apply Subtype.ext
    exact he
  · intro he
    exact congrArg Subtype.val he

end PolishSpaceBook.SetTheoryModels
