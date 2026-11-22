module

public import PolishSpaceBook.BorelInternalChildFamily
public import PolishSpaceBook.CantorApproximationFamilyChoice
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Child-indexed internal choices with a summable dyadic error budget -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression
universe u

/-- Reserve half of a dyadic target for the sum of the individual errors. -/
def unionApproximationError (k n : ℕ) : ℝ := 1 / (2 : ℝ) ^ (k + 2 + n)

lemma unionApproximationError_pos (k n : ℕ) : 0 < unionApproximationError k n := by
  unfold unionApproximationError
  positivity

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
lemma unionApproximationError_hasSum (k : ℕ) :
    HasSum (unionApproximationError k) (1 / (2 : ℝ) ^ (k + 1)) := by
  have he : unionApproximationError k = fun n => (1 / (2 : ℝ) ^ (k + 1)) / 2 / 2 ^ n := by
    funext n
    simp only [unionApproximationError, pow_add, pow_one, pow_two]
    ring
  rw [he]
  exact hasSum_geometric_two' _

/-- The child interpretations and both natural-number error parameters have entire graphs in M. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal inputs at a union node
-/
theorem internal_union_input_graphs {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M) (s : List ℕ) (k : ℕ) :
    sequenceGraph (fun n => internalInterpretation M c hw b (s ++ [n])) ∈ M ∧
      sequenceGraph (fun _ => natOrdinal 1) ∈ M ∧
      sequenceGraph (fun n => natOrdinal (2 ^ (k + 2 + n))) ∈ M := by
  have h1 : natOrdinal 1 ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨1, rfl⟩) (omegaOrdinal_mem hM hinf (hsep _))
  exact ⟨internalChildInterpretationGraph_mem hM hinf hpair hunion hpower hsep hrep c hw b hc hb s,
    constantSequenceGraph_mem hM hinf hpair hsep hrep ⟨_, h1⟩,
    shiftedTwoPowerGraph_mem hM hinf hpair hunion hpower hsep hrep (k + 2)⟩

/-- Once internal totality is supplied at the children, all their dyadic witnesses can be chosen internally. -/
theorem internal_child_admissible_family {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hw : WellFounded c.Child)
    (b : ℕ → List ℕ) (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M)
    (s : List ℕ) (k : ℕ) (Ω Mul Pow Add F X F₂ : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (B a d : ℕ → M) (hB : ∀ n, (B n).val = internalInterpretation M c hw b (s ++ [n]))
    (ha : ∀ n, (a n).val = natOrdinal 1) (hd : ∀ n, (d n).val = natOrdinal (2 ^ (k + 2 + n)))
    (htotal : ∀ n, ∃ W V : M, approximationAdmissibleFormula.Realize Empty.elim
      ![Ω, Mul, Pow, Add, F, X, B n, F₂, W, V, a n, d n]) :
    ∃ W V : ℕ → M, sequenceGraph (fun n => pair (W n).val (V n).val) ∈ M ∧
      ∀ n, approximationAdmissibleFormula.Realize Empty.elim
        ![Ω, Mul, Pow, Add, F, X, B n, F₂, W n, V n, a n, d n] := by
  obtain ⟨hGB, hGa, hGd⟩ := internal_union_input_graphs hM hinf hpair hunion hpower hsep hrep c hw b hc hb s k
  apply internal_admissible_family hM hinf hpair hunion hpower hsep hrep hchoice Ω Mul Pow Add F X F₂
    hΩ B a d _ _ _ htotal
  · simpa only [hB] using hGB
  · simpa only [ha] using hGa
  · simpa only [hd] using hGd

end PolishSpaceBook.CantorTreeMeasure
