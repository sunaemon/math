module

public import PolishSpaceBook.SetTheoryOrderTypeCollection
public import PolishSpaceBook.SetTheoryInjectionOrder

@[expose] public section

/-! # An internal ordinal admitting no internal injection into a prescribed set -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Injectivity of $j$ makes $g:D\to H$ a function, and every element of $H$ occurs as one of its values.
    For $x,y\in D$, write $x=j(a)$ and $y=j(b)$ with the uniquely determined $a,b\in H$.
    Then
    $$x=y\quad\Longleftrightarrow\quad a=b,\qquad
     \langle x,y\rangle\in R\quad\Longleftrightarrow\quad a\in b.$$
    Hence $g$ is an order-isomorphism and the recognition lemma gives $M\models\iota(D,R,H,g)$.
    Since $R\IncludedIn D\times D\IncludedIn W\times W$, the collection property gives $H\in T\IncludedIn H$.
    This contradicts $H\notin H$ and proves the bound.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal Hartogs bound
-/
theorem internal_hartogs_bound {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : M ⊨ replacementSentence ordinalCodeFormula) (W : M) :
    ∃ H : M, H.val.IsOrdinal ∧ ∀ f : M, ZFSet.IsFunc H.val W.val f.val →
      ¬ (∀ a b x, pair a x ∈ f.val → pair b x ∈ f.val → a = b) := by
  obtain ⟨H, hH, hbound⟩ := internal_order_type_bound hM hpair hunion hpower hsep hrep W
  refine ⟨H, hH, ?_⟩
  intro f hf hinj
  obtain ⟨D, R, g, hD, hR, hg⟩ := internal_injection_ordinalIso hM hpair hunion hpower hsep H W f hH hf hinj
  exact ZFSet.mem_irrefl H.val (hbound D R H g hD hR hg)

end PolishSpaceBook.SetTheoryModels
