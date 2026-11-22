module

public import PolishSpaceBook.BorelInternalInterpretationFamily
public import PolishSpaceBook.SetTheoryDefinableSequences
public import PolishSpaceBook.SetTheoryInternalWordOperations

@[expose] public section

/-! # Internal input graphs for countable selection at a Borel union node -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters finite words, extension graph, parent, interpretation family, input, output. -/
def childInterpretationPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.conj (binaryMemberAt 1 2 4 6) (.pairMember 3 6 5))

lemma eval_childInterpretationPredicate (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (b : ℕ → List ℕ) (s : List ℕ) (n : ℕ) (y : ZFSet.{u}) :
    childInterpretationPredicate.eval ![finiteSequences, wordSnocGraph, wordGraph s,
      internalInterpretationFamily M c hw b, natOrdinal n, y] ↔
      y = internalInterpretation M c hw b (s ++ [n]) := by
  simp only [childInterpretationPredicate, eval, Fin.snoc, eval_binaryMemberAt]
  change (∃ t ∈ finiteSequences,
    pair (pair (wordGraph s) (natOrdinal n)) t ∈ wordSnocGraph ∧
      pair t y ∈ internalInterpretationFamily M c hw b) ↔ _
  constructor
  · rintro ⟨t, ht, hsnoc, hy⟩
    obtain ⟨w, rfl⟩ := mem_finiteSequences.mp ht
    rw [pair_mem_wordSnocGraph] at hsnoc
    rw [hsnoc, pair_mem_internalInterpretationFamily] at hy
    exact hy
  · intro hy
    exact ⟨wordGraph (s ++ [n]), mem_finiteSequences.mpr ⟨_, rfl⟩,
      (pair_mem_wordSnocGraph _ _ _).mpr rfl, (pair_mem_internalInterpretationFamily _ _ _ _ _ _).mpr hy⟩

/-- Restricting the all-node family along the child-address map preserves an internal whole graph. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal inputs at a union node
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Let $\Gamma$ be the internal graph of one-entry extension from §{sec:internal-finite-tests}. The value
    $B_{s\concat\SingletonSeq{n}}$ is recognized by the bounded condition
    $$\exists \tau\in F\;[\Pair{\Pair{e(s)}{n}}{\tau}\in \Gamma
    \land\Pair{\tau}{D}\in\mathcal I_c].$$
    The first lookup forces $\tau=e(s\concat\SingletonSeq{n})$ and the second forces $D=B_n$.
    The uniform interpretation principle and graph collection therefore give $G_B\in M$.
    This argument uses the entire graph $\mathcal I_c$ as a parameter.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The constant value $a_n=1$ is recognized by equality. Write $G_+$ for the internal addition graph and
    $P_2$ for the power graph of §{sec:internal-finite-measure-bounds}. The value $b_n$ is recognized by
    $$\exists j\in\omega\;[\Pair{\Pair{k+2}{n}}{j}\in G_+
    \land\Pair{j}{d}\in P_2].$$
    Its unique value is $d=2^{k+2+n}$. Apply the same graph-collection principle to each of these two
    bounded definitions. Reindexing the collected graphs by actual natural numbers preserves the graphs,
    so $G_a,G_b\in M$. Finally, the geometric-series identity gives the asserted sum of the errors.
-/
theorem internalChildInterpretationGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M) (s : List ℕ) :
    sequenceGraph (fun n => internalInterpretation M c hw b (s ++ [n])) ∈ M := by
  let F : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let E : M := ⟨_, (finiteWordOperationGraphs_mem hM hinf hpair hunion hpower hsep).2.2⟩
  let S : M := ⟨wordGraph s, hM.mem_trans (mem_finiteSequences.mpr ⟨s, rfl⟩) F.property⟩
  let I : M := ⟨_, internalInterpretationFamily_mem hM hinf hpair hunion hpower hsep hrep c hw b hc hb⟩
  let values (n : ℕ) : M := ⟨internalInterpretation M c hw b (s ++ [n]),
    internalInterpretation_mem hM hinf hpair hunion hpower hsep c hw b hc hb _⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep childInterpretationPredicate ![F, E, S, I] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![F, E, S, I]) (natOrdinal n)) y.val =
      ![finiteSequences, wordSnocGraph, wordGraph s, internalInterpretationFamily M c hw b, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_childInterpretationPredicate]
  constructor
  · intro he
    apply Subtype.ext
    exact he
  · intro he
    exact congrArg Subtype.val he

end PolishSpaceBook.BorelExpression
