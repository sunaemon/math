module

public import PolishSpaceBook.SetTheoryInternalListCodes
public import PolishSpaceBook.BorelInternalInterpretation
public import PolishSpaceBook.BorelExpressionNatCertificates

@[expose] public section

/-! # Internal standard cylinder enumeration and numerical Borel labels

The standard basis-word graph is the internal list decoder. Composing that
decoder with the label graph also constructs the numerical label table used
by finite Borel-certificate tests.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels NamedLambda
universe u

lemma canonicalBasisWordGraph_eq :
    (basisWordGraph NatListCode.decode : ZFSet.{u}) = listDecodeGraph := rfl

/-- The standard cylinder enumeration is derived, rather than supplied as an extra input. -/
theorem canonicalBasisWordGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (basisWordGraph NatListCode.decode : ZFSet.{u}) ∈ M :=
  listDecodeGraph_mem hM hinf hpair hunion hpower hsep

/-- For the canonical cylinders, only the label graph remains an input parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Internal standard cylinder interpretation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The basis-word graph is exactly $D$. Apply the internal-interpretation theorem in §{sec:internal-borel-sets}
    with this graph and the given label graph. The earlier membership comparison with the external evaluation is
    unchanged.
-/
theorem canonical_internalInterpretation_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (hc : c.labelGraph ∈ M) (w : List ℕ) :
    internalInterpretation M c hw NatListCode.decode w ∈ M :=
  internalInterpretation_mem hM hinf hpair hunion hpower hsep c hw NatListCode.decode hc
    (canonicalBasisWordGraph_mem hM hinf hpair hunion hpower hsep) w

def numericalLabelGraph (c : BorelExpression) : ZFSet.{u} :=
  sequenceGraph (fun n => natOrdinal (c (NatListCode.decode n)))

/-- Parameters omega, finite-word set, decoder, labels, output pair. -/
def numericalLabelPredicate : BoundedSetPredicate 5 :=
  .ex 0 (.ex 0 (.ex 1 (.conj (.orderedPair 4 5 6)
    (.conj (.pairMember 2 5 7) (.pairMember 3 7 6)))))

def numericalLabelFormula : ForcingFormulas.Formula 5 := numericalLabelPredicate.compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The decoder forces $s=e(\LambdaListDecode{n})$, and the label graph then forces
    $a=c(\LambdaListDecode{n})$. Conversely, that finite word graph belongs to $F$ and supplies the witness.
    This identifies the separated set with $L_{\mathrm{num}}$.
-/
lemma eval_numericalLabelPredicate (c : BorelExpression) (p : ZFSet.{u}) :
    numericalLabelPredicate.eval
      ![Ordinal.omega0.toZFSet, finiteSequences, listDecodeGraph, c.labelGraph, p] ↔
      p ∈ c.numericalLabelGraph := by
  change (∃ n ∈ Ordinal.omega0.toZFSet, ∃ a ∈ Ordinal.omega0.toZFSet, ∃ s ∈ finiteSequences,
    p = pair n a ∧ pair n s ∈ listDecodeGraph ∧ pair s a ∈ c.labelGraph) ↔ _
  constructor
  · rintro ⟨n, hn, a, _, s, hs, hp, hdec, hl⟩
    obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp hn
    obtain ⟨w, rfl⟩ := mem_finiteSequences.mp hs
    rw [pair_mem_listDecodeGraph] at hdec
    rw [pair_mem_labelGraph, hdec] at hl
    rw [hp, hl]
    exact (pair_mem_sequenceGraph _ i _).mpr rfl
  · intro hp
    obtain ⟨i, he⟩ := ZFSet.mem_range.mp hp
    exact ⟨natOrdinal i, mem_omegaOrdinal.mpr ⟨i, rfl⟩,
      natOrdinal (c (NatListCode.decode i)), mem_omegaOrdinal.mpr ⟨_, rfl⟩,
      wordGraph (NatListCode.decode i), mem_finiteSequences.mpr ⟨_, rfl⟩, he.symm,
      (pair_mem_listDecodeGraph i _).mpr rfl, (pair_mem_labelGraph c _ _).mpr rfl⟩

/-- The numerical label table used by finite row tests is internal. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal numerical Borel labels
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separate from $\omega\times\omega$ the pairs $\langle n,a\rangle$ satisfying
    $$\exists s\in F\;\bigl(\langle n,s\rangle\in D\land\langle s,a\rangle\in\ell\bigr).$$
-/
theorem numericalLabelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hc : c.labelGraph ∈ M) : c.numericalLabelGraph ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let F : M := ⟨finiteSequences, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let D : M := ⟨listDecodeGraph, listDecodeGraph_mem hM hinf hpair hunion hpower hsep⟩
  let L : M := ⟨c.labelGraph, hc⟩
  apply numericalLabelPredicate.subset_mem hM (hsep _) ![Ω, F, D, L]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
    (sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨_, rfl⟩)).1
  intro p _
  have he : Fin.snoc (Subtype.val ∘ ![Ω, F, D, L]) p =
      ![Ordinal.omega0.toZFSet, finiteSequences, listDecodeGraph, c.labelGraph, p] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact eval_numericalLabelPredicate c p

end PolishSpaceBook.BorelExpression
