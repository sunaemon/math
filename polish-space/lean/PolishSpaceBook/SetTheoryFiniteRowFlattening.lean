module

public import PolishSpaceBook.SetTheoryDefinableSequences
public import PolishSpaceBook.SetTheoryNaturalPairing
public import PolishSpaceBook.SetTheoryInternalSequenceSets

@[expose] public section

/-! # Flattening an entire internal sequence of finite function graphs -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-- Read an entry of a row, with a fixed value at unused columns. -/
def rowValue (E f d : ZFSet.{u}) (i : ℕ) : ZFSet.{u} := by
  classical
  exact if h : ∃ y ∈ E, pair (natOrdinal i) y ∈ f then Classical.choose h else d

lemma rowValue_cases (E f d : ZFSet.{u}) (i : ℕ) :
    (rowValue E f d i ∈ E ∧ pair (natOrdinal i) (rowValue E f d i) ∈ f) ∨
      (rowValue E f d i = d ∧ ¬∃ y ∈ E, pair (natOrdinal i) y ∈ f) := by
  classical
  by_cases he : ∃ y ∈ E, pair (natOrdinal i) y ∈ f
  · exact Or.inl (by simpa only [rowValue, dite_eq_left he] using Classical.choose_spec he)
  · exact Or.inr ⟨by simp only [rowValue, dite_eq_right he], he⟩

lemma rowValue_eq_of_pair {E f d y : ZFSet.{u}} {k i : ℕ}
    (hf : IsFunc (natOrdinal k) E f) (hy : pair (natOrdinal i) y ∈ f) :
    rowValue E f d i = y := by
  have hi := ZFSet.pair_mem_prod.mp (hf.1 hy)
  rcases rowValue_cases E f d i with hr | hr
  · exact (hf.2 _ hi.1).unique hr.2 hy
  · exact False.elim (hr.2 ⟨y, hi.2, hy⟩)

/-- Parameters carrier, row, default, column, output. -/
def rowValuePredicate : BoundedSetPredicate 5 :=
  .disj (.pairMember 1 3 4) (.conj (.equal 4 2) (.neg (.ex 0 (.pairMember 1 3 5))))

lemma eval_rowValuePredicate {E f d : ZFSet.{u}} {k : ℕ}
    (hf : IsFunc (natOrdinal k) E f) (i : ℕ) (y : ZFSet.{u}) :
    rowValuePredicate.eval ![E, f, d, natOrdinal i, y] ↔ y = rowValue E f d i := by
  change (pair (natOrdinal i) y ∈ f ∨
    y = d ∧ ¬∃ z ∈ E, pair (natOrdinal i) z ∈ f) ↔ _
  constructor
  · rintro (hy | ⟨rfl, hn⟩)
    · exact (rowValue_eq_of_pair hf hy).symm
    · simp only [rowValue, dite_eq_right hn]
  · rintro rfl
    rcases rowValue_cases E f d i with hr | hr
    · exact Or.inl hr.2
    · exact Or.inr hr

def flattenRows (E : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (d : ZFSet.{u}) (j : ℕ) : ZFSet.{u} :=
  rowValue E (f j.unpair.1) d j.unpair.2

lemma flattenRows_pair (E : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (d : ZFSet.{u}) (n i : ℕ) :
    flattenRows E f d (Nat.pair n i) = rowValue E (f n) d i := by
  simp only [flattenRows, Nat.unpair_pair]

/-- Parameters omega, numerical pairing, row table, its range, carrier, default, index, output. -/
def flattenRowsPredicate : BoundedSetPredicate 8 :=
  .ex 0 (.ex 0 (.ex 3 (.conj (binaryMemberAt 1 8 9 6)
    (.conj (.pairMember 2 8 10) (rowValuePredicate.rename ![4, 10, 5, 9, 7])))))

lemma eval_flattenRowsPredicate (E : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (d : ZFSet.{u})
    (hf : ∀ n, ∃ k : ℕ, IsFunc (natOrdinal k) E (f n)) (j : ℕ) (y : ZFSet.{u}) :
    flattenRowsPredicate.eval ![Ordinal.omega0.toZFSet, naturalBinaryGraph Nat.pair,
      sequenceGraph f, graphRange (sequenceGraph f), E, d, natOrdinal j, y] ↔
        y = flattenRows E f d j := by
  simp only [flattenRowsPredicate, eval, eval_binaryMemberAt, eval_rename, Fin.snoc]
  change (∃ n ∈ Ordinal.omega0.toZFSet, ∃ i ∈ Ordinal.omega0.toZFSet,
    ∃ row ∈ graphRange (sequenceGraph f), pair (pair n i) (natOrdinal j) ∈ naturalBinaryGraph Nat.pair ∧
    pair n row ∈ sequenceGraph f ∧ rowValuePredicate.eval ![E, row, d, i, y]) ↔ _
  simp only [exists_mem_omegaOrdinal, pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff,
    pair_mem_sequenceGraph]
  constructor
  · rintro ⟨n, i, row, _, hj, hrow, hy⟩
    subst j
    subst row
    obtain ⟨k, hk⟩ := hf n
    rw [flattenRows_pair]
    exact (eval_rowValuePredicate hk i y).mp hy
  · intro hy
    obtain ⟨k, hk⟩ := hf j.unpair.1
    exact ⟨j.unpair.1, j.unpair.2, f j.unpair.1,
      mem_graphRange.mpr ⟨natOrdinal j.unpair.1, (pair_mem_sequenceGraph _ _ _).mpr rfl⟩,
      (Nat.pair_unpair j).symm, rfl, (eval_rowValuePredicate hk _ y).mpr hy⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Flattening internal finite rows
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The numerical pairing graph and $\GraphRange{H}$ belong to $M$. To read a row $f$ at column $i$, require
    $$\langle i,y\rangle\in f\quad\lor\quad
    \bigl(y=d\ \land\ \neg\exists z\in E\;(\langle i,z\rangle\in f)\bigr).$$
    Since $f$ is a function with finite ordinal domain, this bounded predicate specifies exactly one output.
    Given $j$, quantify $n,i$ over $\omega$ and $f$ over $\GraphRange{H}$, require
    $j=\NatPair{n}{i}$ and $\langle n,f\rangle\in H$, and use the row predicate.
    Bounded reflection and graph collection give the entire graph of $V$ in $M$.
    Every output is either $d$ or an entry of a row, and every row entry occurs at its paired index.
    The unused column $k_0$ in row $0$ also gives $V_{\NatPair{0}{k_0}}=d$, proving the range formula.
    The union identity follows because adjoining $\emptyset$ does not change a union.
-/
theorem flattenRows_sequence_mem {M E : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hE : E ∈ M) (f : ℕ → ZFSet.{u}) (hG : sequenceGraph f ∈ M)
    (hf : ∀ n, ∃ k : ℕ, IsFunc (natOrdinal k) E (f n)) (d : M) :
    sequenceGraph (flattenRows E f d.val) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let P : M := ⟨_, naturalPairingGraph_mem hM hinf hpair hunion hpower hsep⟩
  let G : M := ⟨_, hG⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  have hm (j : ℕ) : flattenRows E f d.val j ∈ M := by
    rcases rowValue_cases E (f j.unpair.1) d.val j.unpair.2 with hr | hr
    · exact hM.mem_trans hr.1 hE
    · change rowValue E (f j.unpair.1) d.val j.unpair.2 ∈ M
      rw [hr.1]
      exact d.property
  let values (j : ℕ) : M := ⟨_, hm j⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep flattenRowsPredicate
    ![Ω, P, G, R, ⟨E, hE⟩, d] values
  intro j y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![Ω, P, G, R, ⟨E, hE⟩, d]) (natOrdinal j)) y.val =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph Nat.pair, sequenceGraph f,
        graphRange (sequenceGraph f), E, d.val, natOrdinal j, y.val] := by
    funext i
    fin_cases i <;> rfl
  rw [he, eval_flattenRowsPredicate E f d.val hf]
  exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Flattening internal finite rows
-/
theorem flattenRows_range (E : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (d : ZFSet.{u})
    (hf : ∀ n, ∃ k : ℕ, IsFunc (natOrdinal k) E (f n)) (y : ZFSet.{u}) :
    (∃ j, flattenRows E f d j = y) ↔ y = d ∨ ∃ n, y ∈ graphRange (f n) := by
  constructor
  · rintro ⟨j, rfl⟩
    rcases rowValue_cases E (f j.unpair.1) d j.unpair.2 with hr | hr
    · exact Or.inr ⟨j.unpair.1, mem_graphRange.mpr ⟨natOrdinal j.unpair.2, hr.2⟩⟩
    · exact Or.inl hr.1
  · rintro (rfl | ⟨n, hn⟩)
    · obtain ⟨k, hk⟩ := hf 0
      have hn : ¬∃ y ∈ E, pair (natOrdinal k) y ∈ f 0 := by
        rintro ⟨y, _, hy⟩
        have hi := (ZFSet.pair_mem_prod.mp (hk.1 hy)).1
        exact (Nat.lt_irrefl k) ((natOrdinal_mem_natOrdinal k k).mp hi)
      exact ⟨Nat.pair 0 k, by rw [flattenRows_pair]; simp only [rowValue, dite_eq_right hn]⟩
    · obtain ⟨i, hi⟩ := mem_graphRange.mp hn
      obtain ⟨k, hk⟩ := hf n
      obtain ⟨j, _, rfl⟩ := mem_natOrdinal.mp (ZFSet.pair_mem_prod.mp (hk.1 hi)).1
      exact ⟨Nat.pair n j, by rw [flattenRows_pair]; exact rowValue_eq_of_pair hk hi⟩

theorem flattenRows_empty_union (E : ZFSet.{u}) (f : ℕ → ZFSet.{u})
    (hf : ∀ n, ∃ k : ℕ, IsFunc (natOrdinal k) E (f n)) :
    sequenceUnion (flattenRows E f ∅) = sequenceUnion (fun n => sUnion (graphRange (f n))) := by
  ext x
  simp only [mem_sequenceUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨j, hx⟩
    rcases (flattenRows_range E f ∅ hf _).mp ⟨j, rfl⟩ with hz | ⟨n, hn⟩
    · exact False.elim (ZFSet.notMem_empty x (hz ▸ hx))
    · exact ⟨n, flattenRows E f ∅ j, hn, hx⟩
  · rintro ⟨n, B, hB, hx⟩
    obtain ⟨j, hj⟩ := (flattenRows_range E f ∅ hf B).mpr (Or.inr ⟨n, hB⟩)
    exact ⟨j, hj.symm ▸ hx⟩

end PolishSpaceBook.SetTheoryModels
