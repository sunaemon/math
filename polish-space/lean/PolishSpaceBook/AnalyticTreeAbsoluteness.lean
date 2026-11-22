module

public import PolishSpaceBook.InternalAnalyticSections

@[expose] public section

/-! # Closed-projection truth from internal section trees

The parameter is an old real and the pair-tree code is in the smaller model.
Separation constructs its section there. The rank argument for that section
then transfers analytic truth and its coanalytic negation.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BorelExpression
universe u

/-- The witnesses are the reals available inside the model. -/
def InternalAnalyticTruth (M : ZFSet.{u}) (T : Set (List ℕ × List ℕ)) (x : ℕ → ℕ) : Prop :=
  ∃ y : ℕ → ℕ, pointGraph y ∈ M ∧ (x,y) ∈ pairTreeBody T

theorem internalAnalyticTruth_iff_section (M : ZFSet.{u}) (T : Set (List ℕ × List ℕ)) (x : ℕ → ℕ) :
    InternalAnalyticTruth M T x ↔ HasInternalTreeBranch M (analyticSection T x) := by
  constructor
  · rintro ⟨y, hym, hy⟩
    exact ⟨y, (treeBody_analyticSection T x y).mpr hy, hym⟩
  · rintro ⟨y, hy, hym⟩
    exact ⟨y, hym, (treeBody_analyticSection T x y).mp hy⟩

variable {M N : ZFSet.{u}} (hM : M.IsTransitive) (hN : N.IsTransitive) (hMN : M ⊆ N)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)
include hM hN hMN hinf hpair hunion hpower hsep hrep hchoice

/-- The full analytic assertion is absolute, using its internally constructed section. -/
theorem analytic_tree_absolute (T : Set (List ℕ × List ℕ))
    (hsync : ∀ z ∈ T, z.1.length = z.2.length)
    (hdown : ∀ z ∈ T, ∀ n, (z.1.take n,z.2.take n) ∈ T)
    (hT : pairWordTreeSet T ∈ M) (x : ℕ → ℕ) (hx : pointGraph x ∈ M) :
    InternalAnalyticTruth M T x ↔ InternalAnalyticTruth N T x := by
  rw [internalAnalyticTruth_iff_section, internalAnalyticTruth_iff_section]
  exact tree_branch_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice
    (analyticSection T x) (analyticSection_subtree T hdown x)
    (analyticSection_mem hM hinf hpair hunion hpower hsep T hsync hT x hx)

/-- Negating the analytic normal form gives coanalytic absoluteness. -/
theorem coanalytic_tree_absolute (T : Set (List ℕ × List ℕ))
    (hsync : ∀ z ∈ T, z.1.length = z.2.length)
    (hdown : ∀ z ∈ T, ∀ n, (z.1.take n,z.2.take n) ∈ T)
    (hT : pairWordTreeSet T ∈ M) (x : ℕ → ℕ) (hx : pointGraph x ∈ M) :
    (¬ InternalAnalyticTruth M T x) ↔ ¬ InternalAnalyticTruth N T x :=
  not_congr (analytic_tree_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice
    T hsync hdown hT x hx)

/-- Replacing a closed presentation by its finite approximation tree is compatible
with the internal-witness interpretation in both models. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    For the analytic case, use the closed-projection characterization in §{sec:analytic-sets} and a synchronized
    pair tree $U$ coded in $M$. For a real parameter $a\in M$, put
    $$T_a:=\{t:(\restrict{a}{|t|},t)\in U\}.$$
    This section is coded in $M$. Indeed, code each finite word $s$ by its function graph $e(s)$, and code the nodes
    of $U$ by pairs of these graphs. From the internal set of all finite-word graphs, Separation selects $e(t)$
    when there is a finite-word graph $e(s)$ contained in the graph of $a$ such that the coded pair
    $\langle e(s),e(t)\rangle$ belongs to the code of $U$. Synchronization forces $|s|=|t|$, so this test says
    exactly that $t\in T_a$. Branches through $T_a$ are precisely the witnesses in the closed projection.
    Applying the branch result to $T_a$ proves analytic absoluteness, and negation gives coanalytic absoluteness.
    This proves the $\bSigma^1_1/\bPi^1_1$ case directly. The next argument deduces the
    $\bSigma^1_2/\bPi^1_2$ case from the cited basis theorem.
    \end{proof}
-/
theorem closed_projection_absolute (F : Set ((ℕ → ℕ) × (ℕ → ℕ))) (hF : IsClosed F)
    (hcode : pairWordTreeSet (closedPairTreeCode F) ∈ M) (x : ℕ → ℕ) (hx : pointGraph x ∈ M) :
    (∃ y : ℕ → ℕ, pointGraph y ∈ M ∧ (x,y) ∈ F) ↔
      ∃ y : ℕ → ℕ, pointGraph y ∈ N ∧ (x,y) ∈ F := by
  have h := analytic_tree_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice
    (closedPairTreeCode F) (closedPairTreeCode_synchronized F) (closedPairTreeCode_downward F) hcode x hx
  simpa only [InternalAnalyticTruth, pairTreeBody_closedPairTreeCode F hF] using h

/-- The branch and analytic/coanalytic clauses of the chapter's proposition. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  excerpt: |
    \begin{proposition*}[Analytic/coanalytic absoluteness]\termref{absoluteness}
    Let $M\IncludedIn N$ be transitive models of enough ZFC with the same ordinals, and let $T\in M$ be a subtree of
    $\finseq{\omega}$ or of $\finseq{\omega\times\omega}$. Then "$T$ has an infinite branch" is absolute between $M$ and
    $N$. Consequently, analytic and coanalytic truth with parameters in $M$ is absolute between $M$ and $N$.
    \end{proposition*}
-/
theorem analytic_coanalytic_absolute :
    (∀ (A : Type) (e : A ≃ ℕ) (T : Set (List A)), IsSubtree T →
      wordTreeSet (codedMoveTree e T) ∈ M →
      ((∃ p : ℕ → A, p ∈ treeBody T ∧ pointGraph (e ∘ p) ∈ M) ↔
        ∃ p : ℕ → A, p ∈ treeBody T ∧ pointGraph (e ∘ p) ∈ N)) ∧
    (∀ (T : Set (List ℕ × List ℕ)),
      (∀ z ∈ T, z.1.length = z.2.length) →
      (∀ z ∈ T, ∀ n, (z.1.take n,z.2.take n) ∈ T) → pairWordTreeSet T ∈ M →
      ∀ x : ℕ → ℕ, pointGraph x ∈ M →
      (InternalAnalyticTruth M T x ↔ InternalAnalyticTruth N T x) ∧
      ((¬ InternalAnalyticTruth M T x) ↔ ¬ InternalAnalyticTruth N T x)) := by
  constructor
  · intro A e T ht hw
    exact countable_tree_branch_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice e T ht hw
  · intro T hs hd ht x hx
    exact ⟨analytic_tree_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice T hs hd ht x hx,
      coanalytic_tree_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice T hs hd ht x hx⟩

end PolishSpaceBook.SetTheoryModels
