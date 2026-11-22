module

public import PolishSpaceBook.NonnegativeRealCutAddition

@[expose] public section

/-! # Bounded arithmetic constructs sums of internal real codes -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters omega, multiplication, addition, a,b,c,d,e,f. -/
def rationalSumLessPredicate : BoundedSetPredicate 9 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0
    (.conj (binaryMemberAt 1 6 8 9)
      (.conj (binaryMemberAt 1 3 9 10)
        (.conj (binaryMemberAt 1 5 8 11)
          (.conj (binaryMemberAt 1 7 6 12)
            (.conj (binaryMemberAt 2 11 12 13)
              (.conj (binaryMemberAt 1 13 4 14) (.member 10 14))))))))))))

lemma eval_rationalSumLessPredicate (a b c d e f : ℕ) :
    rationalSumLessPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y),
      natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d, natOrdinal e, natOrdinal f] ↔
        a * (d * f) < (c * f + e * d) * b := by
  simp [rationalSumLessPredicate, eval, eval_binaryMemberAt, Fin.snoc, exists_mem_omegaOrdinal,
    pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff]
  norm_cast

/-- Parameters zero, cut, numerator, denominator. -/
def cutLowerApproximationPredicate : BoundedSetPredicate 4 :=
  .conj (.member 0 3) (.disj (.equal 2 0) (.pairMember 1 2 3))

lemma eval_cutLowerApproximationPredicate (C : ZFSet.{u}) (a b : ℕ) :
    cutLowerApproximationPredicate.eval ![∅, C, natOrdinal a, natOrdinal b] ↔
      cutLowerApproximation C a b := by
  change (∅ ∈ natOrdinal b ∧ (natOrdinal a = ∅ ∨ pair (natOrdinal a) (natOrdinal b) ∈ C)) ↔ _
  simp only [← natOrdinal_zero, natOrdinal_mem_natOrdinal, natOrdinal_injective.eq_iff,
    cutLowerApproximation]

/-- Parameters omega, multiplication, addition, zero, C,D,a,b,c,d,e,f. -/
def sumCutMarginPredicate : BoundedSetPredicate 12 :=
  .conj (.member 3 7)
    (.conj (cutLowerApproximationPredicate.rename ![3, 4, 8, 9])
      (.conj (cutLowerApproximationPredicate.rename ![3, 5, 10, 11])
        (rationalSumLessPredicate.rename ![0, 1, 2, 6, 7, 8, 9, 10, 11])))

lemma eval_sumCutMarginPredicate (C D : ZFSet.{u}) (a b c d e f : ℕ) :
    sumCutMarginPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y), ∅,
      C, D, natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d, natOrdinal e, natOrdinal f] ↔
      0 < b ∧ cutLowerApproximation C c d ∧ cutLowerApproximation D e f ∧
        a * (d * f) < (c * f + e * d) * b := by
  let ps : Fin 12 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y), ∅,
    C, D, natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d, natOrdinal e, natOrdinal f]
  have ec : ps ∘ ![(3 : Fin 12), 4, 8, 9] = ![∅, C, natOrdinal c, natOrdinal d] := by
    funext i; fin_cases i <;> rfl
  have ed : ps ∘ ![(3 : Fin 12), 5, 10, 11] = ![∅, D, natOrdinal e, natOrdinal f] := by
    funext i; fin_cases i <;> rfl
  have es : ps ∘ ![(0 : Fin 12), 1, 2, 6, 7, 8, 9, 10, 11] = ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y),
      natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d, natOrdinal e, natOrdinal f] := by
    funext i; fin_cases i <;> rfl
  change sumCutMarginPredicate.eval ps ↔ _
  simp only [sumCutMarginPredicate, eval, eval_rename, ec, ed, es,
    eval_cutLowerApproximationPredicate, eval_rationalSumLessPredicate]
  change (∅ ∈ natOrdinal b ∧ _) ↔ _
  simp only [← natOrdinal_zero, natOrdinal_mem_natOrdinal]

/-- Parameters omega, multiplication, addition, zero, C,D, proposed pair. -/
def sumCutPredicate : BoundedSetPredicate 7 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0
    (.conj (.orderedPair 6 7 8)
      (sumCutMarginPredicate.rename ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12])))))))

lemma eval_sumCutPredicate (C D z : ZFSet.{u}) :
    sumCutPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y), ∅, C, D, z] ↔
      ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ 0 < b ∧ ∃ c d e f : ℕ,
        cutLowerApproximation C c d ∧ cutLowerApproximation D e f ∧
          a * (d * f) < (c * f + e * d) * b := by
  let ps : Fin 7 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y), ∅, C, D, z]
  have he (a b c d e f : ZFSet.{u}) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps a) b) c) d) e) f ∘
        ![(0 : Fin 13), 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
        naturalBinaryGraph (fun x y => x + y), ∅, C, D, a, b, c, d, e, f] := by
    funext i; fin_cases i <;> rfl
  change sumCutPredicate.eval ps ↔ _
  simp only [sumCutPredicate, eval, eval_rename, he]
  change (∃ a ∈ Ordinal.omega0.toZFSet, ∃ b ∈ Ordinal.omega0.toZFSet,
    ∃ c ∈ Ordinal.omega0.toZFSet, ∃ d ∈ Ordinal.omega0.toZFSet,
    ∃ e ∈ Ordinal.omega0.toZFSet, ∃ f ∈ Ordinal.omega0.toZFSet,
      z = pair a b ∧ sumCutMarginPredicate.eval ![Ordinal.omega0.toZFSet,
        naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y), ∅,
        C, D, a, b, c, d, e, f]) ↔ _
  simp only [exists_mem_omegaOrdinal, eval_sumCutMarginPredicate]
  constructor
  · rintro ⟨a, b, c, d, e, f, hz, hb, hc, hd, hlt⟩
    exact ⟨a, b, hz, hb, c, d, e, f, hc, hd, hlt⟩
  · rintro ⟨a, b, hz, hb, c, d, e, f, hc, hd, hlt⟩
    exact ⟨a, b, c, d, e, f, hz, hb, hc, hd, hlt⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal addition of real cut codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Use the internal graphs of natural addition and multiplication from §{sec:internal-natural-arithmetic}.
    The displayed membership condition has only $\omega$-bounded witnesses. To express its arithmetic comparison,
    perform the following six computations:
    $$\begin{aligned}
    t_1&=df,& t_2&=at_1,& t_3&=cf,\\
    t_4&=ed,& t_5&=t_3+t_4,& t_6&=t_5b.
    \end{aligned}$$
    Then test $t_2<t_6$. The outputs of the computations are also bounded by $\omega$.
    The shared bounded-interpretation theorem therefore identifies this condition inside $M$ with the
    external one. Separation on $\omega\times\omega$ constructs precisely $\RealCutSum{C}{D}$ in $M$.
    The preceding theorem identifies its decoded value.
-/
theorem sumCutCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {C D : ZFSet.{u}} (hC : C ∈ M) (hD : D ∈ M) : sumCutCode C D ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let Mul : M := ⟨_, naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep⟩
  let Add : M := ⟨_, naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩
  let E : M := ⟨_, empty_mem_of_infinity hM hinf⟩
  let ps : Fin 6 → M := ![Ω, Mul, Add, E, ⟨C, hC⟩, ⟨D, hD⟩]
  unfold sumCutCode naturalPairSet
  apply separation_mem_of_absolute hM sumCutPredicate.compile (hsep _) ps
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
  intro z _
  rw [sumCutPredicate.realize_compile hM]
  have he : Subtype.val ∘ Fin.snoc ps z = ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun x y => x * y), naturalBinaryGraph (fun x y => x + y), ∅, C, D, z.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_sumCutPredicate]

end PolishSpaceBook.CantorTreeMeasure
