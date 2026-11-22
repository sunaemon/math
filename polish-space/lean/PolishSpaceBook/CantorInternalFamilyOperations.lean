module

public import PolishSpaceBook.CantorInternalSelectedFamily
public import PolishSpaceBook.SetTheorySequenceOperations

@[expose] public section

/-! # Extracting internal inner-tree and outer-open families from selected pairs -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression
universe u

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Operations on entire approximation families
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Write $R=\operatorname{ran}(\mathcal H)$ and $Q=\bigcup\bigcup R$. These sets belong to $M$ by the range and
    union operations. Both components of each pair in $R$ lie in $Q$. For $n\in\omega$, the bounded condition
    $$\exists z\in R\;\exists \alpha\in Q\;\exists \beta\in Q\;
    [\Pair{n}{z}\in \mathcal H\land z=\Pair{\alpha}{\beta}\land y=\alpha]$$
    holds exactly when $y=W_{T_n}$. Replacing $y=\alpha$ by $y=\beta$ recognizes $W_{S_n}$.
    Apply the shared bounded-interpretation and graph-collection principles to obtain $G_T,G_S\in M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For the third graph, use the internal set $F_2$ of binary-word graphs and $R_S=\operatorname{ran}(G_S)$.
    The output $D$ at $n$ is characterized by
    $$\begin{gathered}
    \exists \beta\in R_S\;[\Pair{n}{\beta}\in G_S
    \land D\IncludedIn F_2\\
    {}\land\forall \sigma\in F_2\;(\sigma\in D\longleftrightarrow \sigma\notin \beta)].
    \end{gathered}$$
    Its unique value is $D=\SetDifference{F_2}{W_{S_n}}=W_{O_n}$, which is internal by Separation.
    The same interpretation and graph-collection principles give $G_O\in M$.
    Now apply the open-union and finite-tree-union constructions of §{sec:internal-finite-measure-bounds}.
    They give the two combined codes in the statement.
-/
theorem approximation_family_graphs_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T S : ℕ → Set (List Bool)) (hT : ∀ n, wordTreeSet (binaryLift (T n)) ∈ M)
    (hS : ∀ n, wordTreeSet (binaryLift (S n)) ∈ M)
    (hH : sequenceGraph (fun n => pair (wordTreeSet (binaryLift (T n))) (wordTreeSet (binaryLift (S n)))) ∈ M) :
    sequenceGraph (fun n => wordTreeSet (binaryLift (T n))) ∈ M ∧
      sequenceGraph (fun n => wordTreeSet (binaryLift (S n))) ∈ M ∧
      sequenceGraph (fun n => wordTreeSet (binaryLift (S n)ᶜ)) ∈ M := by
  let W (n : ℕ) : M := ⟨_, hT n⟩
  let V (n : ℕ) : M := ⟨_, hS n⟩
  have hW := pairSequence_projection_mem hM hinf hpair hunion hsep hrep W V hH true
  have hV := pairSequence_projection_mem hM hinf hpair hunion hsep hrep W V hH false
  refine ⟨hW, hV, ?_⟩
  rw [show (fun n => wordTreeSet (binaryLift (S n)ᶜ)) =
    (fun n => (wordTreeSet (binaryLift Set.univ)).sep (fun x => x ∉ wordTreeSet (binaryLift (S n))))
    from funext (fun n => wordTreeSet_binary_compl (S n))]
  exact sequenceRelativeComplement_mem hM hinf hpair hunion hsep hrep
    ⟨_, binaryWords_mem hM hinf hpair hunion hpower hsep⟩ V hV

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Operations on entire approximation families
-/
theorem approximation_union_codes_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T S : ℕ → Set (List Bool)) (hT : ∀ n, wordTreeSet (binaryLift (T n)) ∈ M)
    (hS : ∀ n, wordTreeSet (binaryLift (S n)) ∈ M)
    (hH : sequenceGraph (fun n => pair (wordTreeSet (binaryLift (T n))) (wordTreeSet (binaryLift (S n)))) ∈ M)
    (N : ℕ) :
    wordTreeSet (binaryLift (⋃ n, (S n)ᶜ)) ∈ M ∧
      wordTreeSet (binaryLift (⋃ n ∈ Finset.range (N + 1), T n)) ∈ M := by
  have hgraphs := approximation_family_graphs_mem hM hinf hpair hunion hpower hsep hrep T S hT hS hH
  exact ⟨openUnion_mem hM hunion hsep _ hgraphs.2.2,
    finiteTreeUnion_mem hM hinf hpair hunion _ T (fun n _ => hT n)⟩

end PolishSpaceBook.CantorTreeMeasure
