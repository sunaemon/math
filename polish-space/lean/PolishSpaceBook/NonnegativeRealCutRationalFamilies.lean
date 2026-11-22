module

public import PolishSpaceBook.NonnegativeRealCutReflection
public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Whole internal families of rational real codes -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters omega, multiplication, zero, numerator, denominator, proposed pair. -/
def fractionCutMemberPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.ex 0 (.conj (.orderedPair 5 6 7) (.conj (.member 2 7)
    (rationalLessPredicate.rename ![0, 1, 6, 7, 3, 4]))))

lemma eval_fractionCutMemberPredicate (m d : ℕ) (hd : 0 < d) (z : ZFSet.{u}) :
    fractionCutMemberPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), ∅, natOrdinal m, natOrdinal d, z] ↔
      z ∈ nonnegativeRealCutCode ((m : ℝ) / d) := by
  let ps : Fin 6 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun x y => x * y), ∅, natOrdinal m, natOrdinal d, z]
  have he (a b : ZFSet.{u}) : Fin.snoc (Fin.snoc ps a) b ∘ ![(0 : Fin 8), 1, 6, 7, 3, 4] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y), a, b, natOrdinal m, natOrdinal d] := by
    funext i; fin_cases i <;> rfl
  change fractionCutMemberPredicate.eval ps ↔ _
  simp only [fractionCutMemberPredicate, eval, eval_rename, he]
  change (∃ a ∈ Ordinal.omega0.toZFSet, ∃ b ∈ Ordinal.omega0.toZFSet,
    z = pair a b ∧ ∅ ∈ b ∧ rationalLessPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), a, b, natOrdinal m, natOrdinal d]) ↔ _
  simp only [exists_mem_omegaOrdinal, eval_rationalLessPredicate, ← natOrdinal_zero,
    natOrdinal_mem_natOrdinal, mem_nonnegativeRealCutCode]
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  exact and_congr_right (fun _ => and_congr_right (fun hb => rationalLess_iff a b m d hb hd))

lemma fractionCutCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (m d : ℕ) (hd : 0 < d) : nonnegativeRealCutCode ((m : ℝ) / d) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let Mul : M := ⟨_, naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep⟩
  let E : M := ⟨_, empty_mem_of_infinity hM hinf⟩
  let ps : Fin 5 → M := ![Ω, Mul, E, ⟨natOrdinal m, hn m⟩, ⟨natOrdinal d, hn d⟩]
  apply fractionCutMemberPredicate.subset_mem hM (hsep _) ps
    (B := nonnegativeRealCutCode ((m : ℝ) / d))
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
    (by
      intro z hz
      unfold nonnegativeRealCutCode naturalPairSet at hz
      exact (ZFSet.mem_sep.mp hz).1)
  intro z _
  have he : Fin.snoc (Subtype.val ∘ ps) z = ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), ∅, natOrdinal m, natOrdinal d, z] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_fractionCutMemberPredicate m d hd]

/-- Parameters omega, multiplication, zero, natural-pair ambient set, m,d,C. -/
def fractionCutValuePredicate : BoundedSetPredicate 7 :=
  .conj (.subset 6 3) (.all 0 (.all 0 (.iff (.pairMember 6 7 8)
    (.conj (.member 2 8) (rationalLessPredicate.rename ![0, 1, 7, 8, 4, 5])))))

lemma eval_fractionCutValuePredicate (m d : ℕ) (hd : 0 < d) (C : ZFSet.{u}) :
    fractionCutValuePredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), ∅,
      prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, natOrdinal m, natOrdinal d, C] ↔
      C = nonnegativeRealCutCode ((m : ℝ) / d) := by
  let ps : Fin 7 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun x y => x * y), ∅,
    prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, natOrdinal m, natOrdinal d, C]
  have he (a b : ZFSet.{u}) : Fin.snoc (Fin.snoc ps a) b ∘ ![(0 : Fin 9), 1, 7, 8, 4, 5] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y), a, b, natOrdinal m, natOrdinal d] := by
    funext i; fin_cases i <;> rfl
  change fractionCutValuePredicate.eval ps ↔ _
  simp only [fractionCutValuePredicate, eval, eval_rename, he]
  change (C ⊆ prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet ∧
    ∀ a ∈ Ordinal.omega0.toZFSet, ∀ b ∈ Ordinal.omega0.toZFSet,
      pair a b ∈ C ↔ ∅ ∈ b ∧ rationalLessPredicate.eval ![Ordinal.omega0.toZFSet,
        naturalBinaryGraph (fun x y => x * y), a, b, natOrdinal m, natOrdinal d]) ↔ _
  simp only [forall_mem_omegaOrdinal, eval_rationalLessPredicate, ← natOrdinal_zero,
    natOrdinal_mem_natOrdinal]
  unfold nonnegativeRealCutCode
  rw [← naturalPairSet_characterization]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro a
  apply forall_congr'
  intro b
  exact iff_congr Iff.rfl (and_congr_right (fun hb => rationalLess_iff a b m d hb hd))

/-- Parameters omega, multiplication, zero, pairs, numerator graph, denominator graph, n, C. -/
def fractionCutSequencePredicate : BoundedSetPredicate 8 :=
  .ex 0 (.ex 0 (.conj (.pairMember 4 6 8) (.conj (.pairMember 5 6 9)
    (fractionCutValuePredicate.rename ![0, 1, 2, 3, 8, 9, 7]))))

lemma eval_fractionCutSequencePredicate (m d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (n : ℕ) (C : ZFSet.{u}) :
    fractionCutSequencePredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), ∅, prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet,
      sequenceGraph (fun n => natOrdinal (m n)), sequenceGraph (fun n => natOrdinal (d n)), natOrdinal n, C] ↔
      C = nonnegativeRealCutCode ((m n : ℝ) / d n) := by
  let ps : Fin 8 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun x y => x * y), ∅, prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet,
    sequenceGraph (fun n => natOrdinal (m n)), sequenceGraph (fun n => natOrdinal (d n)), natOrdinal n, C]
  have he (a b : ZFSet.{u}) : Fin.snoc (Fin.snoc ps a) b ∘ ![(0 : Fin 10), 1, 2, 3, 8, 9, 7] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y), ∅,
        prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, a, b, C] := by
    funext i; fin_cases i <;> rfl
  change fractionCutSequencePredicate.eval ps ↔ _
  simp only [fractionCutSequencePredicate, eval, eval_rename, he]
  change (∃ a ∈ Ordinal.omega0.toZFSet, ∃ b ∈ Ordinal.omega0.toZFSet,
    pair (natOrdinal n) a ∈ sequenceGraph (fun n => natOrdinal (m n)) ∧
      pair (natOrdinal n) b ∈ sequenceGraph (fun n => natOrdinal (d n)) ∧
        fractionCutValuePredicate.eval ![Ordinal.omega0.toZFSet,
          naturalBinaryGraph (fun x y => x * y), ∅,
          prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, a, b, C]) ↔ _
  simp only [pair_mem_sequenceGraph]
  constructor
  · rintro ⟨a, _, b, _, rfl, rfl, h⟩
    exact (eval_fractionCutValuePredicate (m n) (d n) (hd n) C).mp h
  · intro h
    exact ⟨_, mem_omegaOrdinal.mpr ⟨m n, rfl⟩, _, mem_omegaOrdinal.mpr ⟨d n, rfl⟩,
      rfl, rfl, (eval_fractionCutValuePredicate (m n) (d n) (hd n) C).mpr h⟩

/-- Entire rational-value families are internal when both entire integer families are internal. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal families of rational value codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For fixed $m,d\in\omega$ with $d>0$, the membership test is
    $$\langle a,b\rangle\in\NonnegativeRealCut{m/d}
    \quad\longleftrightarrow\quad 0<b\ \land\ ad<mb.$$
    The multiplication graph expresses this condition by bounded quantifiers. Shared bounded interpretation
    and Separation on $\omega\times\omega$ therefore construct the whole cut inside $M$.
    A subset of $\omega\times\omega$ is uniquely determined by these pair-membership tests.
    Given $n$, read $m_n,d_n$ from the two internal graphs, and characterize the output by those tests.
    The shared graph-collection theorem then gives the graph of all the output cuts by Replacement.
-/
theorem fractionCutCode_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (m d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (hmM : sequenceGraph (fun n => natOrdinal (m n)) ∈ M)
    (hdM : sequenceGraph (fun n => natOrdinal (d n)) ∈ M) :
    sequenceGraph (fun n => nonnegativeRealCutCode ((m n : ℝ) / d n)) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let Mul : M := ⟨_, naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep⟩
  let E : M := ⟨_, empty_mem_of_infinity hM hinf⟩
  let P : M := ⟨_, prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property⟩
  let ps : Fin 6 → M := ![Ω, Mul, E, P, ⟨_, hmM⟩, ⟨_, hdM⟩]
  let values (n : ℕ) : M := ⟨_, fractionCutCode_mem hM hinf hpair hunion hpower hsep (m n) (d n) (hd n)⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep fractionCutSequencePredicate ps values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y), ∅,
        prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, sequenceGraph (fun n => natOrdinal (m n)),
        sequenceGraph (fun n => natOrdinal (d n)), natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_fractionCutSequencePredicate m d hd]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end PolishSpaceBook.CantorTreeMeasure
