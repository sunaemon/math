module

public import PolishSpaceBook.ForcingGroundCovers
public import PolishSpaceBook.ForcingPairing
public import PolishSpaceBook.SetTheoryChoiceEnumeration
public import PolishSpaceBook.SetTheoryChoiceFromCovers

@[expose] public section

/-! # Preservation of Choice by transporting ground enumerations through internal covers -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingNames ForcingAtomic ForcingFormulas
universe u

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence) (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
include hM hinf hpair hunion hpower hsep hrep hchoice hR

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $N:=M[G]$. The earlier constructions show that $N$ is transitive, contains $M$, and satisfies
    Pairing, Union, and Replacement. Fix a family $A\in N$ whose members are nonempty, and put
    $$X:=\bigcup A\in N.$$
    The ground-set cover theorem supplies $D\in M$ and $U,F\in N$ with
    $$U\IncludedIn D,\qquad F:U\twoheadrightarrow X.$$
    §{sec:internal-choice-enumerations} supplies an ordinal $\gamma\in M$ and a bijection
    $e:\gamma\to D$ with its graph in $M$.
    Since $M\IncludedIn N$, the sets $\gamma,D,e$ belong to $N$.
    They are the same actual ordinal, set, and function graph, so $e$ remains a bijection onto $D$ in the extension.
    This transports the required enumeration; no ground-model membership of $U$ is needed.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the preservation of Choice, this reduces the problem to ordering inputs from a single ground-model set.
    §{sec:internal-choice-enumerations} derives an internal ordinal enumeration from the ground model's
    Choice axiom. §{sec:generic-choice} transports that enumeration to the extension and uses least
    preimages to construct a choice graph there.
-/
theorem extension_ordinal_cover (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    (X : Extension P.val M G) : HasOrdinalCover (Extension P.val M G) X.val := by
  have hg : ∃ p ∈ chosen P.val G, p ∈ P.val := by
    obtain ⟨q, hq⟩ := G.nonempty
    exact ⟨q.val, ⟨q, hq, rfl⟩, q.property⟩
  have hME := ground_subset_extension_of_axioms hM hinf hpair hunion hpower hsep hrep P.property
    (chosen P.val G) hg
  obtain ⟨D, U, F, hUD, hF, hFonto⟩ := extension_ground_cover hM hinf hpair hunion hpower hsep hrep P R hR G hG X
  obtain ⟨γ, e, hγ, he, heonto, _⟩ := internal_choice_enumeration hM hinf hpair hunion hpower hsep hrep hchoice D
  exact ⟨⟨γ.val, hME γ.property⟩, ⟨D.val, hME D.property⟩, U, ⟨e.val, hME e.property⟩, F,
    hγ, he, heonto, hUD, hF, hFonto⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Choice in generic extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finally, §{sec:generic-choice} combines the ground-set covers with internal ordinal enumerations and collects
    least-preimage choice graphs inside the extension. This proves preservation of Choice without well-ordering
    the proper class of all names.
-/
theorem extension_models_choice (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    Extension P.val M G ⊨ choiceSentence := by
  have hg : ∃ p ∈ chosen P.val G, p ∈ P.val := by
    obtain ⟨q, hq⟩ := G.nonempty
    exact ⟨q.val, ⟨q, hq, rfl⟩, q.property⟩
  have hN := extension_isTransitive P.val M (chosen P.val G) hM
  have hpairN := extension_models_pairing hM hinf hpair hunion hpower (hrep _) P.property (chosen P.val G) hg
  have hunionN := extension_models_union hM hinf hpair hunion hpower (hrep _) (hrep _) P.property R.property hR G
  have hrepN := extension_models_replacement hM hinf hpair hunion hpower hsep hrep P R hR G hG
    (graphSelector leastOrdinalChoiceFormula)
  exact models_choice_of_ordinal_covers hN hpairN hunionN hrepN
    (extension_ordinal_cover hM hinf hpair hunion hpower hsep hrep hchoice P R hR G hG)

end Model
end PolishSpaceBook.SetTheoryModels
