module

public import PolishSpaceBook.BorelFiniteRows

@[expose] public section

/-! # Bounded row selection without an extra numerical maximum graph -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels NamedLambda
open BoundedSetPredicate
universe u

lemma certificatePrefixBound_le_iff (i n : ℕ) : certificatePrefixBound i ≤ n ↔
    NatListCode.encode (rowWord i) < n ∧ NatListCode.encode (rowChild i) < n ∧
      0 < n ∧ (rowLeaf i).length ≤ n := by
  simp [certificatePrefixBound, Nat.add_one_le_iff, NatListCode.encode]

lemma getD_take_below (q : List ℕ) {i n : ℕ} (hi : i < n) : (q.take n).getD i 0 = q.getD i 0 := by
  by_cases hq : i < q.length
  · have htake : i < (q.take n).length := by simp [List.length_take, hi, hq]
    rw [List.getD_eq_getElem _ _ htake, List.getD_eq_getElem _ _ hq]
    simp
  · rw [List.getD_eq_default _ _ (by simp only [List.length_take]; omega),
      List.getD_eq_default _ _ (Nat.le_of_not_gt hq)]

/-- All observations of a row lie below its bound, including default-zero lookup. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Finally, all lookups in row $i$ occur below $b(i)$, and its leaf
    word has length at most $b(i)$. Hence
    $$P_i(\restrict{a}{b(i)},\restrict{d}{b(i)})\quad\Longleftrightarrow\quad P_i(a,d).$$
    This holds even for shorter words: default-zero lookup is unchanged by a cutoff above the queried coordinate,
    and two successive restrictions compose by taking the smaller cutoff.
-/
lemma finiteCertificateClause_take (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ) :
    finiteCertificateClause c b i (x.take (certificatePrefixBound i), q.take (certificatePrefixBound i)) ↔
      finiteCertificateClause c b i (x, q) := by
  obtain ⟨hs, ht, hr, hl⟩ := (certificatePrefixBound_le_iff i _).mp (le_refl _)
  simp only [finiteCertificateClause, NatListCode.encode, getD_take_below q hr,
    getD_take_below q hs, getD_take_below q ht, List.take_take, Nat.min_eq_left hl]

/-- Existing row parameters followed by the available length. -/
def rowFitsBody : BoundedSetPredicate 22 :=
  .conj (.pairMember 7 12 17)
  (.conj (.pairMember 8 12 18)
  (.conj (binaryMemberAt 9 17 18 19)
  (.conj (.pairMember 11 18 20)
  (.conj (.function 21 0 20)
  (.conj (.member 17 16)
  (.conj (.member 19 16)
  (.conj (.member 2 16) (.neg (.member 16 21)))))))))

def rowFitsPredicate : BoundedSetPredicate 17 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 1 (.ex 0 rowFitsBody))))

lemma eval_rowFitsBody (xs : Fin 22 → ZFSet.{u}) : rowFitsBody.eval xs ↔
    pair (xs 12) (xs 17) ∈ xs 7 ∧ pair (xs 12) (xs 18) ∈ xs 8 ∧
    pair (pair (xs 17) (xs 18)) (xs 19) ∈ xs 9 ∧ pair (xs 18) (xs 20) ∈ xs 11 ∧
    IsFunc (xs 21) (xs 0) (xs 20) ∧ xs 17 ∈ xs 16 ∧ xs 19 ∈ xs 16 ∧
    xs 2 ∈ xs 16 ∧ xs 16 ∉ xs 21 := by
  simp only [rowFitsBody, eval, eval_binaryMemberAt]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For the row-selection condition, put $n=|a|$ using $L$. The definition of $b$ gives
    $$b(i)\le n\quad\Longleftrightarrow\quad
    p<n\land t<n\land0<n\land|\LambdaListDecode{k}|\le n.$$
    The decoder and $L$ give the last length, so this too is a bounded predicate.
-/
lemma eval_rowFitsPredicate (c : BorelExpression) (b : Bool) (i n : ℕ) (x q : List ℕ) :
    rowFitsPredicate.eval (Fin.snoc (finiteRowParams.{u} c b i x q) (natOrdinal n)) ↔
      certificatePrefixBound i ≤ n := by
  simp [rowFitsPredicate, eval_rowFitsBody, eval, finiteRowParams, Fin.snoc,
    exists_mem_omegaOrdinal, exists_mem_finiteSequences, pair_mem_sequenceGraph,
    listDecodeGraph, pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff,
    wordGraph_injective.eq_iff, wordLength_iff,
    certificatePrefixBound_le_iff, rowWord, rowChild, rowLeaf, NatListCode.encode_decode]

/-- Bind the input length, then inspect every row below that length whose observations fit. -/
def boundedRowsPredicate : BoundedSetPredicate 16 :=
  .ex 0 (.conj (.function 16 0 13)
    (.all 16 ((rowFitsPredicate.rename ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 13, 14, 15, 16]).imply
      (finiteRowPredicate.rename ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 13, 14, 15]))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Bounded description of finite Borel tests
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Bind the row index by $i\in n$
    and use implication to select the rows that fit.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Therefore $V$ is exactly the bounded
    family of row tests used in the counterexample tree.
-/
lemma eval_boundedRowsPredicate (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ) :
    boundedRowsPredicate.eval (finiteRowParams.{u} c b i x q) ↔
      LambdaTree.boundedPrefixTest (finiteCertificateClause c b) certificatePrefixBound (x, q) := by
  simp only [boundedRowsPredicate, eval, eval_imply, eval_rename]
  change (∃ n ∈ Ordinal.omega0.toZFSet, IsFunc n Ordinal.omega0.toZFSet (wordGraph x) ∧
    ∀ j ∈ n,
      rowFitsPredicate.eval ((Fin.snoc (Fin.snoc (finiteRowParams c b i x q) n) j) ∘
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 13, 14, 15, 16]) →
      finiteRowPredicate.eval ((Fin.snoc (Fin.snoc (finiteRowParams c b i x q) n) j) ∘
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 13, 14, 15])) ↔ _
  rw [exists_mem_omegaOrdinal]
  simp only [wordLength_iff, exists_eq_left]
  have he (j : ℕ) :
      Fin.snoc (Fin.snoc (finiteRowParams.{u} c b i x q) (natOrdinal x.length)) (natOrdinal j) ∘
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 13, 14, 15, 16] =
      Fin.snoc (finiteRowParams c b j x q) (natOrdinal x.length) := by funext k; fin_cases k <;> rfl
  have hf (j : ℕ) :
      Fin.snoc (Fin.snoc (finiteRowParams.{u} c b i x q) (natOrdinal x.length)) (natOrdinal j) ∘
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 13, 14, 15] =
      finiteRowParams c b j x q := by funext k; fin_cases k <;> rfl
  constructor
  · intro h j hj hb
    have h' := h (natOrdinal j) (mem_natOrdinal.mpr ⟨j, hj, rfl⟩)
    rw [he j, hf j, eval_rowFitsPredicate, eval_finiteRowPredicate] at h'
    exact (finiteCertificateClause_take c b j x q).mpr (h' hb)
  · intro h j hj
    obtain ⟨j, hj, rfl⟩ := mem_natOrdinal.mp hj
    rw [he j, hf j, eval_rowFitsPredicate, eval_finiteRowPredicate]
    intro hb
    exact (finiteCertificateClause_take c b j x q).mp (h j (by simpa using hj) hb)

/-- The whole selected family is interpreted by the same reflection as each row. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The uniform interpretation principle applies to the
    whole assembled predicates.
-/
theorem boundedRowsPredicate_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ)
    (hparams : ∀ j, finiteRowParams c b i x q j ∈ M) :
    boundedRowsPredicate.compile.Realize Empty.elim
      (fun j => ⟨finiteRowParams c b i x q j, hparams j⟩ : Fin 16 → M) ↔
        LambdaTree.boundedPrefixTest (finiteCertificateClause c b) certificatePrefixBound (x, q) :=
  (boundedRowsPredicate.realize_compile hM _).trans (eval_boundedRowsPredicate c b i x q)

end PolishSpaceBook.BorelExpression
