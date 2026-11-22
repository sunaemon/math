module

public import PolishSpaceBook.CantorInternalMeasureFormula
public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Entire internal families of finite levels and their cardinalities -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

/-- Collect the finite-level sets using the already verified bounded level predicate. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal finite-level families
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The finite-level predicate of §{sec:internal-finite-measure-bounds} defines $L_n$ uniquely, and each $L_n$
    belongs to the model by Separation. Bounded interpretation followed by graph collection gives $G_L$.
    For $G_k$, use the already verified finite-cardinality formula, requiring the output to belong to $\omega$.
    That formula holds exactly when the output is $k_n$. Graph collection by Replacement therefore gives $G_k$.
    This uses the existing interpretation theorem for finite bijections; no new selection of bijections is needed.
-/
theorem finiteWordLevel_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T : Set (List ℕ)) (hT : wordTreeSet T ∈ M) :
    sequenceGraph (finiteWordLevel T) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let W : M := ⟨_, hT⟩
  let values (n : ℕ) : M := ⟨_, finiteWordLevel_mem hM hinf hsep T hT n⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep finiteLevelPredicate ![Ω, W] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![Ω, W]) (natOrdinal n)) y.val =
      ![Ordinal.omega0.toZFSet, wordTreeSet T, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_finiteLevelPredicate]
  constructor
  · intro he
    exact Subtype.ext he
  · intro he
    exact congrArg Subtype.val he

/-- The output is required to be a natural number before testing the finite cardinality. -/
def naturalLevelCardinalityFormula : ForcingFormulas.Formula 4 :=
  (BoundedSetPredicate.member (3 : Fin 4) 0).compile ⊓ levelCardinalityFormula

/-- Collect the actual finite counts, without choosing new cardinality witnesses externally. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal finite-level families
-/
theorem levelCardinality_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) :
    sequenceGraph (fun n => natOrdinal (level T n).card) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let W : M := ⟨_, hT⟩
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let values (n : ℕ) : M := ⟨_, hn (level T n).card⟩
  apply definable_sequenceGraph_mem hM hinf hpair hsep hrep naturalLevelCardinalityFormula
    ![Ω, W] values
  intro n N y hN
  have he : Fin.snoc (Fin.snoc ![Ω, W] N) y = ![Ω, W, N, y] := by
    funext i; fin_cases i <;> rfl
  rw [he, naturalLevelCardinalityFormula, BoundedFormula.realize_inf,
    BoundedSetPredicate.realize_compile hM]
  change (y.val ∈ Ordinal.omega0.toZFSet ∧
    levelCardinalityFormula.Realize Empty.elim ![Ω, W, N, y]) ↔ y = values n
  constructor
  · rintro ⟨hy, hc⟩
    obtain ⟨k, hk⟩ := mem_omegaOrdinal.mp hy
    have hc := (realize_levelCardinalityFormula hM hinf hpair hunion hsep T n k Ω W N y
      rfl rfl hN hk.symm).mp hc
    apply Subtype.ext
    exact hk.symm.trans (congrArg natOrdinal hc)
  · rintro rfl
    exact ⟨mem_omegaOrdinal.mpr ⟨_, rfl⟩,
      (realize_levelCardinalityFormula hM hinf hpair hunion hsep T n _ Ω W N (values n)
        rfl rfl hN rfl).mpr rfl⟩

end PolishSpaceBook.CantorTreeMeasure
