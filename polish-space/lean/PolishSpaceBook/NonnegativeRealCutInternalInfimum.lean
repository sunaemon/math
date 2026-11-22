module

public import PolishSpaceBook.NonnegativeRealCutInfimum

@[expose] public section

/-! # Internal construction of a countable infimum code from the entire sequence graph -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters omega, multiplication, zero, sequence graph, range, a,b,m,d. -/
def infCutMarginPredicate : BoundedSetPredicate 9 :=
  .conj (.member 2 6) (.conj (.member 2 8)
    (.conj (rationalLessPredicate.rename ![0, 1, 5, 6, 7, 8])
      (.all 0 (.ex 4 (.conj (.pairMember 3 9 10) (.pairMember 10 7 8))))))

lemma eval_infCutMarginPredicate (C : ℕ → ZFSet.{u}) (a b m d : ℕ) :
    infCutMarginPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun a b => a * b), ∅, sequenceGraph C, graphRange (sequenceGraph C),
      natOrdinal a, natOrdinal b, natOrdinal m, natOrdinal d] ↔
      0 < b ∧ 0 < d ∧ a * d < m * b ∧ ∀ n, pair (natOrdinal m) (natOrdinal d) ∈ C n := by
  let ps : Fin 9 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun a b => a * b), ∅, sequenceGraph C, graphRange (sequenceGraph C),
    natOrdinal a, natOrdinal b, natOrdinal m, natOrdinal d]
  have e : ps ∘ ![(0 : Fin 9), 1, 5, 6, 7, 8] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b),
        natOrdinal a, natOrdinal b, natOrdinal m, natOrdinal d] := by
    funext i; fin_cases i <;> rfl
  change infCutMarginPredicate.eval ps ↔ _
  simp only [infCutMarginPredicate, eval, eval_rename, e, eval_rationalLessPredicate]
  change (∅ ∈ natOrdinal b ∧ ∅ ∈ natOrdinal d ∧ a * d < m * b ∧
    ∀ N ∈ Ordinal.omega0.toZFSet, ∃ D ∈ graphRange (sequenceGraph C),
      pair N D ∈ sequenceGraph C ∧ pair (natOrdinal m) (natOrdinal d) ∈ D) ↔ _
  simp only [← natOrdinal_zero, natOrdinal_mem_natOrdinal, forall_mem_omegaOrdinal,
    pair_mem_sequenceGraph]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h n
    obtain ⟨D, _, rfl, hm⟩ := h n
    exact hm
  · intro h n
    exact ⟨C n, mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph _ n _).mpr rfl⟩, rfl, h n⟩

/-- The candidate pair is the last parameter; all four fraction integers are bounded witnesses. -/
def roundedInfCutPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 0 (.conj (.orderedPair 5 6 7)
    (infCutMarginPredicate.rename ![0, 1, 2, 3, 4, 6, 7, 8, 9])))))

lemma eval_roundedInfCutPredicate (C : ℕ → ZFSet.{u}) (z : ZFSet.{u}) :
    roundedInfCutPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun a b => a * b), ∅, sequenceGraph C, graphRange (sequenceGraph C), z] ↔
      ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ 0 < b ∧
        ∃ m d : ℕ, 0 < d ∧ a * d < m * b ∧ ∀ n, pair (natOrdinal m) (natOrdinal d) ∈ C n := by
  let ps : Fin 6 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun a b => a * b), ∅, sequenceGraph C, graphRange (sequenceGraph C), z]
  have e (a b m d : ZFSet.{u}) : Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps a) b) m) d ∘
      ![(0 : Fin 10), 1, 2, 3, 4, 6, 7, 8, 9] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b), ∅,
        sequenceGraph C, graphRange (sequenceGraph C), a, b, m, d] := by
    funext i; fin_cases i <;> rfl
  change roundedInfCutPredicate.eval ps ↔ _
  simp only [roundedInfCutPredicate, eval, eval_rename, e]
  change (∃ a ∈ Ordinal.omega0.toZFSet, ∃ b ∈ Ordinal.omega0.toZFSet,
    ∃ m ∈ Ordinal.omega0.toZFSet, ∃ d ∈ Ordinal.omega0.toZFSet,
      z = pair a b ∧ infCutMarginPredicate.eval ![Ordinal.omega0.toZFSet,
        naturalBinaryGraph (fun a b => a * b), ∅, sequenceGraph C, graphRange (sequenceGraph C),
        a, b, m, d]) ↔ _
  simp only [exists_mem_omegaOrdinal, eval_infCutMarginPredicate]
  constructor
  · rintro ⟨a, b, m, d, he, hb, hd, hl, hm⟩
    exact ⟨a, b, he, hb, m, d, hd, hl, hm⟩
  · rintro ⟨a, b, he, hb, m, d, hd, hl, hm⟩
    exact ⟨a, b, m, d, he, hb, hd, hl, hm⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal infimum of real cut codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The range $R=\operatorname{ran}(G)$ belongs to $M$. In the defining condition, replace the test in each term by
    $$\forall n\in\omega\;\exists D\in R\;
    [\Pair{n}{D}\in G\land\Pair{m}{d}\in D].$$
    Since $G$ is the entire graph, this is exactly membership in every $D_n$.
    All witnesses are bounded by $\omega$ or $R$. The cross-product comparison uses the multiplication graph
    from §{sec:internal-natural-arithmetic}. Thus the shared bounded-interpretation theorem applies, and
    Separation on $\omega\times\omega$ constructs exactly $\RealCutInfimum{\mathcal D}$ inside the model.
    The preceding theorem identifies its decoded value. Termwise internality alone would not provide the
    parameter $G$ required by this construction.
-/
theorem roundedInfCutCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (C : ℕ → ZFSet.{u}) (hG : sequenceGraph C ∈ M) : roundedInfCutCode C ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let Mul : M := ⟨_, naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep⟩
  let E : M := ⟨_, empty_mem_of_infinity hM hinf⟩
  let G : M := ⟨_, hG⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let ps : Fin 5 → M := ![Ω, Mul, E, G, R]
  unfold roundedInfCutCode naturalPairSet
  apply separation_mem_of_absolute hM roundedInfCutPredicate.compile (hsep _) ps
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
  intro z _
  rw [roundedInfCutPredicate.realize_compile hM]
  have he : Subtype.val ∘ Fin.snoc ps z =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b), ∅,
        sequenceGraph C, graphRange (sequenceGraph C), z.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_roundedInfCutPredicate]

end PolishSpaceBook.CantorTreeMeasure
