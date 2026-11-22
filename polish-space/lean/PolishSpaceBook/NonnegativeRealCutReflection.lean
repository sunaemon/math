module

public import PolishSpaceBook.NonnegativeRealCutDecode

@[expose] public section

/-! # Absolute recognition and ordering of nonnegative real cut codes -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- All predicates use parameters omega, multiplication, zero, one, and the cut. -/
def cutTypedPredicate : BoundedSetPredicate 5 :=
  .all 4 (.ex 0 (.ex 0 (.conj (.orderedPair 5 6 7) (.member 2 7))))

def cutLowerPredicate : BoundedSetPredicate 5 :=
  .all 0 (.all 0 (.all 0 (.all 0
    ((BoundedSetPredicate.conj (.member (2 : Fin 9) 6) (.conj (.member 2 8) (.conj (.pairMember 4 7 8)
      (.neg (rationalLessPredicate.rename ![0, 1, 7, 8, 5, 6]))))).imply (.pairMember 4 5 6)))))

def cutRoundedPredicate : BoundedSetPredicate 5 :=
  .all 0 (.all 0 ((BoundedSetPredicate.pairMember (4 : Fin 7) 5 6).imply
    (.ex 0 (.ex 0 (.conj (.pairMember 4 7 8)
      (rationalLessPredicate.rename ![0, 1, 5, 6, 7, 8]))))))

def cutBoundedPredicate : BoundedSetPredicate 5 := .ex 0 (.neg (.pairMember 4 5 3))

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Call a set $C$ a \termdefine{nonnegative real cut code} if it satisfies the following four conditions.
    All variables $a,b,m,d,N$ in these conditions range over $\omega$.

    1. Every member of $C$ is a pair $\Pair{a}{b}$ with $0<b$.
    2. If $0<b$, $0<d$, $ad\le mb$, and $\Pair{m}{d}\in C$, then $\Pair{a}{b}\in C$.
    3. If $\Pair{a}{b}\in C$, there are $m,d$ with $\Pair{m}{d}\in C$ and $ad<mb$.
    4. There is an $N$ such that $\Pair{N}{1}\notin C$.

    The second condition includes equality of fractions, so all representations of the same fraction give the
    same membership answer. The third excludes a largest fraction. The empty code is allowed.
    Write $\RealCutCondition{C}$ for the conjunction of these conditions, with the fixed parameters
    $\omega,G_\times,0,1$ understood.
-/
def nonnegativeRealCutPredicate : BoundedSetPredicate 5 :=
  .conj cutTypedPredicate (.conj cutLowerPredicate (.conj cutRoundedPredicate cutBoundedPredicate))

def realCutParameters (C : ZFSet.{u}) : Fin 5 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b), ∅, natOrdinal 1, C]

lemma realCutParameters_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (C : ZFSet.{u}) (hC : C ∈ M) : ∀ i, realCutParameters C i ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  intro i
  fin_cases i
  · exact hΩ
  · exact naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep
  · exact empty_mem_of_infinity hM hinf
  · exact hM.mem_trans (mem_omegaOrdinal.mpr ⟨1, rfl⟩) hΩ
  · exact hC

lemma eval_cutTypedPredicate (C : ZFSet.{u}) :
    cutTypedPredicate.eval (realCutParameters C) ↔
      ∀ z ∈ C, ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ 0 < b := by
  change (∀ z ∈ C, ∃ a ∈ Ordinal.omega0.toZFSet, ∃ b ∈ Ordinal.omega0.toZFSet,
    z = pair a b ∧ ∅ ∈ b) ↔ _
  simp only [exists_mem_omegaOrdinal, ← natOrdinal_zero, natOrdinal_mem_natOrdinal]

lemma eval_cutLowerPredicate (C : ZFSet.{u}) :
    cutLowerPredicate.eval (realCutParameters C) ↔
      ∀ a b m n : ℕ, 0 < b → 0 < n → a * n ≤ m * b →
        pair (natOrdinal m) (natOrdinal n) ∈ C → pair (natOrdinal a) (natOrdinal b) ∈ C := by
  have e (a b m n : ZFSet.{u}) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (realCutParameters C) a) b) m) n ∘
        ![(0 : Fin 9), 1, 7, 8, 5, 6] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b), m, n, a, b] := by
    funext i; fin_cases i <;> rfl
  simp only [cutLowerPredicate, eval, eval_imply, eval_rename, e]
  change (∀ a ∈ Ordinal.omega0.toZFSet, ∀ b ∈ Ordinal.omega0.toZFSet,
    ∀ m ∈ Ordinal.omega0.toZFSet, ∀ n ∈ Ordinal.omega0.toZFSet,
      (∅ ∈ b ∧ ∅ ∈ n ∧ pair m n ∈ C ∧
        ¬ rationalLessPredicate.eval ![Ordinal.omega0.toZFSet,
          naturalBinaryGraph (fun a b => a * b), m, n, a, b]) → pair a b ∈ C) ↔ _
  simp only [forall_mem_omegaOrdinal, eval_rationalLessPredicate,
    ← natOrdinal_zero, natOrdinal_mem_natOrdinal, Nat.not_lt]
  constructor
  · intro h a b m n hb hn hle hmem
    exact h a b m n ⟨hb, hn, hmem, hle⟩
  · intro h a b m n ⟨hb, hn, hmem, hle⟩
    exact h a b m n hb hn hle hmem

lemma eval_cutRoundedPredicate (C : ZFSet.{u}) :
    cutRoundedPredicate.eval (realCutParameters C) ↔
      ∀ a b : ℕ, pair (natOrdinal a) (natOrdinal b) ∈ C →
        ∃ m n : ℕ, pair (natOrdinal m) (natOrdinal n) ∈ C ∧ a * n < m * b := by
  have e (a b m n : ZFSet.{u}) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (realCutParameters C) a) b) m) n ∘
        ![(0 : Fin 9), 1, 5, 6, 7, 8] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b), a, b, m, n] := by
    funext i; fin_cases i <;> rfl
  simp only [cutRoundedPredicate, eval, eval_imply, eval_rename, e]
  change (∀ a ∈ Ordinal.omega0.toZFSet, ∀ b ∈ Ordinal.omega0.toZFSet,
    pair a b ∈ C → ∃ m ∈ Ordinal.omega0.toZFSet, ∃ n ∈ Ordinal.omega0.toZFSet,
      pair m n ∈ C ∧ rationalLessPredicate.eval ![Ordinal.omega0.toZFSet,
        naturalBinaryGraph (fun a b => a * b), a, b, m, n]) ↔ _
  simp only [forall_mem_omegaOrdinal, exists_mem_omegaOrdinal, eval_rationalLessPredicate]

lemma eval_cutBoundedPredicate (C : ZFSet.{u}) :
    cutBoundedPredicate.eval (realCutParameters C) ↔ ∃ N : ℕ, pair (natOrdinal N) (natOrdinal 1) ∉ C := by
  change (∃ N ∈ Ordinal.omega0.toZFSet, pair N (natOrdinal 1) ∉ C) ↔ _
  exact exists_mem_omegaOrdinal _

lemma eval_nonnegativeRealCutPredicate (C : ZFSet.{u}) :
    nonnegativeRealCutPredicate.eval (realCutParameters C) ↔ ValidNonnegativeRealCutCode C := by
  simp only [nonnegativeRealCutPredicate, eval, eval_cutTypedPredicate, eval_cutLowerPredicate,
    eval_cutRoundedPredicate, eval_cutBoundedPredicate]
  exact ⟨fun ⟨ht, hl, hr, hb⟩ => ⟨ht, hl, hr, hb⟩, fun h => ⟨h.typed, h.lower, h.rounded, h.bounded⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Absolute validity of real cut codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The first condition quantifies only over $C$ and $\omega$. The remaining conditions quantify only over
    $\omega$. Express products by bounded lookups in $G_\times$ and comparisons by finite-ordinal membership
    and equality. The ordered-pair predicates are bounded as well. Thus the shared bounded-interpretation
    theorem transfers the conjunction exactly between the model and the external universe.
    Apply the preceding decoding theorem. The required arithmetic parameters belong to the model under the
    hypotheses used in §{sec:internal-natural-arithmetic}.
-/
theorem realize_nonnegativeRealCutPredicate {M : ZFSet.{u}} (hM : M.IsTransitive)
    (ps : Fin 5 → M) (C : ZFSet.{u}) (hp : Subtype.val ∘ ps = realCutParameters C) :
    nonnegativeRealCutPredicate.compile.Realize Empty.elim ps ↔
      ∃ r : ℝ, 0 ≤ r ∧ C = nonnegativeRealCutCode r := by
  rw [nonnegativeRealCutPredicate.realize_compile hM, hp, eval_nonnegativeRealCutPredicate,
    validNonnegativeRealCutCode_iff]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Order of nonnegative real codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    An inequality $r\le s$ preserves every strict lower query. If instead $s<r$, a nonnegative rational strictly
    between them belongs to the cut of $r$ and not to the cut of $s$, contradicting inclusion.
    Inclusion of the two internal sets is a bounded predicate, so the shared interpretation theorem also
    proves the internal assertion.
-/
theorem realize_realCut_order {M : ZFSet.{u}} (hM : M.IsTransitive)
    (R S : M) (r s : ℝ) (hs : 0 ≤ s)
    (hR : R.val = nonnegativeRealCutCode r) (hS : S.val = nonnegativeRealCutCode s) :
    (BoundedSetPredicate.subset (0 : Fin 2) 1).compile.Realize Empty.elim ![R, S] ↔ r ≤ s := by
  rw [BoundedSetPredicate.realize_compile hM]
  change R.val ⊆ S.val ↔ _
  rw [hR, hS, nonnegativeRealCutCode_subset_iff hs]

end PolishSpaceBook.CantorTreeMeasure
