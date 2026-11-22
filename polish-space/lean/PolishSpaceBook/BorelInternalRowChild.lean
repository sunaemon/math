module

public import PolishSpaceBook.SetTheoryInternalWordOperations
public import PolishSpaceBook.SetTheoryInternalListCodes
public import PolishSpaceBook.LambdaBorelEvaluation

@[expose] public section

/-! # Internal numerical graph for appending a child index to a coded Borel node -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas NamedLambda
universe u

/-- Decoder witnesses are explicitly bounded by the finite-word set. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Use the decoder graph $D$ and the extension graph $\mathcal J$. The output equation $k=h(i,j)$ is equivalent to
    $$\begin{aligned}
    \exists s,t\in F\;[&\langle i,s\rangle\in D
    \land\langle\langle s,j\rangle,t\rangle\in\mathcal J\\
    &{}\land\langle k,t\rangle\in D].
    \end{aligned}$$
-/
def SetCodedWordSnoc (F D H i j k : ZFSet.{u}) : Prop :=
  ∃ s ∈ F, ∃ t ∈ F, pair i s ∈ D ∧ pair (pair s j) t ∈ H ∧ pair k t ∈ D

/-- Parameters finite-word set, list decoder, snoc graph, input code, child index, output code. -/
def codedWordSnocPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.ex 0 (.conj (.pairMember 1 3 6)
    (.conj (binaryMemberAt 2 6 4 7) (.pairMember 1 5 7))))

def codedWordSnocFormula : ForcingFormulas.Formula 6 := codedWordSnocPredicate.compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Both witnesses are bounded by the internal set $F$. Expand the binary-graph condition by the bounded
    ordered-pair predicate, so the displayed formula is $\Delta_0$.
-/
lemma codedWordSnocFormula_deltaZero : IsDeltaZero codedWordSnocFormula :=
  codedWordSnocPredicate.compile_deltaZero

lemma realize_codedWordSnocFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (F D H i j k : M) :
    codedWordSnocFormula.Realize Empty.elim ![F, D, H, i, j, k] ↔
      SetCodedWordSnoc F.val D.val H.val i.val j.val k.val := by
  simpa [codedWordSnocFormula, codedWordSnocPredicate, BoundedSetPredicate.eval,
    eval_binaryMemberAt, SetCodedWordSnoc, Fin.snoc, Fin.castPred, Fin.castLT] using
    codedWordSnocPredicate.realize_compile hM ![F, D, H, i, j, k]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The decoder first fixes
    $s=e(\LambdaListDecode{i})$; extension fixes the new word; its second use and the inverse-numbering identities
    fix the output code. Conversely, those two finite graphs supply the witnesses.
-/
lemma setCodedWordSnoc_nat (i j k : ℕ) :
    SetCodedWordSnoc.{u} finiteSequences listDecodeGraph wordSnocGraph
      (natOrdinal i) (natOrdinal j) (natOrdinal k) ↔
        k = NatListCode.encode (NatListCode.decode i ++ [j]) := by
  constructor
  · rintro ⟨s, _, t, _, hs, hh, ht⟩
    have hs' := (pair_mem_sequenceGraph (fun n => wordGraph (NatListCode.decode n)) i s).mp hs
    have ht' := (pair_mem_sequenceGraph (fun n => wordGraph (NatListCode.decode n)) k t).mp ht
    rw [hs', ht', pair_mem_wordSnocGraph] at hh
    simpa only [NatListCode.encode_decode] using congrArg NatListCode.encode hh
  · intro hk
    refine ⟨wordGraph (NatListCode.decode i), mem_finiteSequences.mpr ⟨_, rfl⟩,
      wordGraph (NatListCode.decode i ++ [j]), mem_finiteSequences.mpr ⟨_, rfl⟩,
      (pair_mem_listDecodeGraph i _).mpr rfl, (pair_mem_wordSnocGraph _ _ _).mpr rfl, ?_⟩
    apply (pair_mem_listDecodeGraph k _).mpr
    rw [hk, NatListCode.decode_encode]

/-- The code operation is exactly the one computed by the existing lambda child term. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal child-code graph
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The uniform interpretation
    principle gives the same equivalence internally, and the graph-collection argument uses Separation in
    $(\omega\times\omega)\times\omega$ to obtain the graph.
-/
theorem codedWordSnocGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (naturalBinaryGraph (fun i j => NatListCode.encode (NatListCode.decode i ++ [j])) : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let D : M := ⟨listDecodeGraph, listDecodeGraph_mem hM hinf hpair hunion hpower hsep⟩
  let H : M := ⟨wordSnocGraph, (finiteWordOperationGraphs_mem hM hinf hpair hunion hpower hsep).2.2⟩
  let F : M := ⟨finiteSequences, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  rw [naturalBinaryGraph_eq_ternaryRelationGraph _ _ setCodedWordSnoc_nat]
  apply ternaryRelationGraph_mem hM hpair hunion hpower hsep codedWordSnocFormula F D H Ω Ω Ω
  exact realize_codedWordSnocFormula hM F D H

/-- Reading the graph at the two components of a row index gives the actual child code. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Substituting the numerical projections of the row index
    recovers the child operation already computed by the lambda term in §{sec:lambda-recursive-borel-separation}.
-/
lemma codedWordSnocGraph_row (i k : ℕ) :
    pair (pair (natOrdinal i.unpair.1) (natOrdinal i.unpair.2)) (natOrdinal k) ∈
      (naturalBinaryGraph (fun a b => NatListCode.encode (NatListCode.decode a ++ [b])) : ZFSet.{u}) ↔
        k = NatListCode.encode (BorelExpression.rowChild i) := by
  rw [pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff]
  rfl

end PolishSpaceBook.SetTheoryModels
