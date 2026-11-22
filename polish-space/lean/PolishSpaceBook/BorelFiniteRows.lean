module

public import PolishSpaceBook.BorelFiniteRowArithmetic
public import PolishSpaceBook.BorelCanonicalBasis

@[expose] public section

/-! # A bounded predicate for the complete finite Borel-certificate row -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels NamedLambda
open BoundedSetPredicate
universe u

/-- The persistent graph parameters, the row index, the two finite inputs, and the root bit. -/
def finiteRowParams (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ) : Fin 16 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, finiteSequences, natOrdinal 0, natOrdinal 1, natOrdinal 2, natOrdinal 3,
    naturalBinaryGraph (fun a b => a + b), sequenceGraph (fun n => natOrdinal n.unpair.1),
    sequenceGraph (fun n => natOrdinal n.unpair.2),
    naturalBinaryGraph (fun a b => NatListCode.encode (NatListCode.decode a ++ [b])),
    c.numericalLabelGraph, listDecodeGraph, natOrdinal i, wordGraph x, wordGraph q,
    natOrdinal (if b then 1 else 0)]

/-- Eleven numerical values and the finite leaf word complete one row. -/
def finiteRowBody : BoundedSetPredicate 28 :=
  .conj (.pairMember 7 12 16)
  (.conj (.pairMember 8 12 17)
  (.conj (binaryMemberAt 9 16 17 18)
  (.conj (.pairMember 10 16 19)
  (.conj (.pairMember 10 18 20)
  (.conj (wordLookupAt 0 2 14 2 21)
  (.conj (.pairMember 7 21 15)
  (.conj (wordLookupAt 0 2 14 16 22)
  (.conj (.pairMember 7 22 23)
  (.conj (.pairMember 8 22 24)
  (.conj (wordLookupAt 0 2 14 18 25)
  (.conj (.pairMember 7 25 26)
  (.conj (.pairMember 11 17 27)
    (certificateArithmeticAt 2 3 4 5 6 19 20 23 26 24 17 (.subset 27 13))))))))))))))

def finiteRowPredicate : BoundedSetPredicate 16 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0
    (.ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 0 (.ex 1 finiteRowBody)))))))))))

lemma eval_finiteRowBody (xs : Fin 28 → ZFSet.{u}) :
    finiteRowBody.eval xs ↔
      pair (xs 12) (xs 16) ∈ xs 7 ∧ pair (xs 12) (xs 17) ∈ xs 8 ∧
      pair (pair (xs 16) (xs 17)) (xs 18) ∈ xs 9 ∧
      pair (xs 16) (xs 19) ∈ xs 10 ∧ pair (xs 18) (xs 20) ∈ xs 10 ∧
      SetWordLookup (xs 0) (xs 2) (xs 14) (xs 2) (xs 21) ∧ pair (xs 21) (xs 15) ∈ xs 7 ∧
      SetWordLookup (xs 0) (xs 2) (xs 14) (xs 16) (xs 22) ∧ pair (xs 22) (xs 23) ∈ xs 7 ∧
      pair (xs 22) (xs 24) ∈ xs 8 ∧
      SetWordLookup (xs 0) (xs 2) (xs 14) (xs 18) (xs 25) ∧ pair (xs 25) (xs 26) ∈ xs 7 ∧
      pair (xs 17) (xs 27) ∈ xs 11 ∧
      SetCertificateArithmetic (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)
        (xs 19) (xs 20) (xs 23) (xs 26) (xs 24) (xs 17) (xs 27 ⊆ xs 13) := by
  simp only [finiteRowBody, eval, eval_binaryMemberAt, eval_wordLookupAt, eval_certificateArithmeticAt]

lemma exists_mem_finiteSequences (P : ZFSet.{u} → Prop) :
    (∃ x ∈ finiteSequences, P x) ↔ ∃ s : List ℕ, P (wordGraph s) := by
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hx
    exact ⟨s, hp⟩
  · rintro ⟨s, hp⟩
    exact ⟨wordGraph s, mem_finiteSequences.mpr ⟨s, rfl⟩, hp⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    and the leaf condition is
    $$\restrict{a}{|\LambdaListDecode{k}|}=\LambdaListDecode{k}
    \quad\Longleftrightarrow\quad e(\LambdaListDecode{k})\IncludedIn e(a).$$
-/
lemma wordGraph_subset_take_iff (s t : List ℕ) :
    (wordGraph s : ZFSet.{u}) ⊆ wordGraph t ↔ t.take s.length = s := by
  rw [wordGraph_subset_iff, List.prefix_iff_eq_take]
  exact eq_comm

lemma eval_finiteRowPredicate_values (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ) :
    finiteRowPredicate.eval (finiteRowParams.{u} c b i x q) ↔
      ∃ s k t a d qr qs u j qt v : ℕ, ∃ w : List ℕ,
        s = i.unpair.1 ∧ k = i.unpair.2 ∧ t = NatListCode.encode (NatListCode.decode s ++ [k]) ∧
        a = c (NatListCode.decode s) ∧ d = c (NatListCode.decode t) ∧
        qr = q.getD 0 0 ∧ (if b then 1 else 0) = qr.unpair.1 ∧
        qs = q.getD s 0 ∧ u = qs.unpair.1 ∧ j = qs.unpair.2 ∧
        qt = q.getD t 0 ∧ v = qt.unpair.1 ∧ w = NatListCode.decode k ∧
        certificateArithmetic a d u v j k (x.take w.length = w) := by
  simp [finiteRowPredicate, eval_finiteRowBody, eval, finiteRowParams, Fin.snoc,
    exists_mem_omegaOrdinal, exists_mem_finiteSequences, pair_mem_sequenceGraph,
    numericalLabelGraph, listDecodeGraph, pair_mem_naturalBinaryGraph,
    natOrdinal_injective.eq_iff, setWordLookup_iff,
    wordGraph_injective.eq_iff, setCertificateArithmetic_nat, wordGraph_subset_take_iff]


/-- Every auxiliary value is forced by the input; the remaining conditions are the original row test. -/
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
    Use the two projection graphs to write $i=\NatPair{p}{k}$, and use the child-code graph to obtain $t=h(p,k)$.
    Read the labels at $p,t$ from $L_{\mathrm{num}}$, and read $r(d,0),r(d,p),r(d,t)$ using $R$.
    Project these last three values to obtain the root bit, the two node bits, and the selected child index.
    Every numerical auxiliary variable is bounded by $\omega$; the decoder supplies the leaf word in $F$.
    For $P_i^\varepsilon$, the root bit must equal the finite ordinal $\varepsilon\in M$; all other conditions
    are unchanged. In particular, root bit $0$ gives precisely the absent-node, union, complement,
    and leaf clauses defining $P_i$.
-/
theorem eval_finiteRowPredicate (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ) :
    finiteRowPredicate.eval (finiteRowParams.{u} c b i x q) ↔ finiteCertificateClause c b i (x, q) := by
  rw [eval_finiteRowPredicate_values]
  constructor
  · rintro ⟨s, k, t, a, d, qr, qs, u, j, qt, v, w,
      rfl, rfl, rfl, rfl, rfl, rfl, hroot, rfl, rfl, rfl, rfl, rfl, rfl, hrow⟩
    simpa only [finiteCertificateClause, rowWord, rowChild, rowLeaf,
      NatListCode.decode_encode, NatListCode.encode_decode, NatListCode.encode] using And.intro hroot.symm hrow
  · intro h
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _,
      rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · simpa only [NatListCode.encode] using h.1.symm
    · simpa only [rowWord, rowChild, rowLeaf, NatListCode.decode_encode,
        NatListCode.encode_decode] using h.2

/-- All parameters of a row are internal when the Borel label graph is. -/
theorem finiteRowParams_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hc : c.labelGraph ∈ M) (b : Bool) (i : ℕ) (x q : List ℕ) :
    ∀ j, finiteRowParams c b i x q j ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hF := finiteSequences_mem hM hinf hpair hunion hpower hsep
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  have hw (s : List ℕ) : wordGraph s ∈ M := hM.mem_trans (mem_finiteSequences.mpr ⟨s, rfl⟩) hF
  have hA := naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep
  have hP := naturalProjectionGraph_mem hM hinf hpair hunion hpower hsep true
  have hQ := naturalProjectionGraph_mem hM hinf hpair hunion hpower hsep false
  have hH := codedWordSnocGraph_mem hM hinf hpair hunion hpower hsep
  have hL := numericalLabelGraph_mem hM hinf hpair hunion hpower hsep c hc
  have hD := listDecodeGraph_mem hM hinf hpair hunion hpower hsep
  intro j
  fin_cases j <;> simp only [finiteRowParams] <;>
    first | exact hΩ | exact hF | exact hn _ | exact hw _ | exact hA | exact hP | exact hQ |
      exact hH | exact hL | exact hD

/-- Internal interpretation of the entire finite row follows from the common reflection theorem. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The uniform interpretation principle applies to the
    whole assembled predicates.
-/
theorem finiteRowPredicate_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (c : BorelExpression) (b : Bool) (i : ℕ) (x q : List ℕ)
    (hparams : ∀ j, finiteRowParams c b i x q j ∈ M) :
    finiteRowPredicate.compile.Realize Empty.elim (fun j => ⟨finiteRowParams c b i x q j, hparams j⟩ : Fin 16 → M) ↔
      finiteCertificateClause c b i (x, q) :=
  (finiteRowPredicate.realize_compile hM _).trans (eval_finiteRowPredicate c b i x q)

end PolishSpaceBook.BorelExpression
