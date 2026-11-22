module

public import PolishSpaceBook.ForcingCheckClosure
public import PolishSpaceBook.SetTheoryRankClosure
public import PolishSpaceBook.ForcingOrdinalBounds

@[expose] public section

/-! # Ordinals and Infinity in extensions, with closure derived from ground axioms -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames
universe u

/-- A transitive domain containing the actual ω satisfies the first-order Infinity sentence. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The earlier natural-number construction gives the actual $\omega\in M$, and check-name closure gives
    $M\IncludedIn M[G]$. Hence $\omega\in M[G]$. The extension is transitive, so it contains
    $\emptyset\in\omega$ and, for each $n\in\omega$, the actual successor $n\cup\{n\}\in\omega$.
    These sets satisfy the internal empty-set and successor clauses: their members already lie in the extension.
    Thus the actual natural-number set witnesses the first-order Infinity sentence in the extension.
    \end{proof}
-/
lemma models_infinity_of_omegaOrdinal_mem {S : ZFSet.{u}} (hS : S.IsTransitive)
    (hω : Ordinal.omega0.toZFSet ∈ S) : S ⊨ infinitySentence := by
  apply (models_infinity_iff S).mpr
  have hzero : (∅ : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet := mem_omegaOrdinal.mpr ⟨0, natOrdinal_zero⟩
  refine ⟨⟨Ordinal.omega0.toZFSet, hω⟩,
    ⟨⟨∅, hS.mem_trans hzero hω⟩, hzero, fun z => ZFSet.notMem_empty z.val⟩, ?_⟩
  intro y hy
  have hsucc : insert y.val y.val ∈ Ordinal.omega0.toZFSet := by
    obtain ⟨n, hn⟩ := mem_omegaOrdinal.mp hy
    exact mem_omegaOrdinal.mpr ⟨n + 1, by rw [natOrdinal_succ, hn]⟩
  refine ⟨⟨insert y.val y.val, hS.mem_trans hsucc hω⟩, hsucc, ?_⟩
  intro w
  rw [ZFSet.mem_insert_iff]
  exact ⟨fun h => h.elim (fun he => Or.inr (Subtype.ext he)) Or.inl,
    fun h => h.elim Or.inr (fun he => Or.inl (congrArg Subtype.val he))⟩

/-- Ground axioms imply ordinal preservation, rather than assuming rank or check-name closure. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Ordinal preservation
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The proof separates the external rank estimate from the internal closure constructions.
    The latter have now been derived from the stated axioms. For a weaker ground theory, it is enough to supply
    rank and check-name closure separately and then use the same ordinal comparison.
-/
theorem ordinal_mem_extension_iff_of_axioms {M P α : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hP : P ∈ M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) (hα : α.IsOrdinal) :
    α ∈ extension P M G ↔ α ∈ M :=
  ordinal_mem_extension_iff hM
    (fun τ hτ => rank_mem_of_axioms hM hinf hpair hunion hpower hsep hrep ⟨τ, hτ⟩)
    (fun a ha => check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep ⟨P, hP⟩ ⟨a, ha⟩)
    G hG hα

/-- The actual ω in the ground model witnesses Infinity in the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Infinity in the extension
-/
theorem extension_models_infinity {M P : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hP : P ∈ M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) : extension P M G ⊨ infinitySentence :=
  models_infinity_of_omegaOrdinal_mem (extension_isTransitive P M G hM)
    (ground_subset_extension_of_axioms hM hinf hpair hunion hpower hsep hrep hP G hG
      (omegaOrdinal_mem hM hinf (hsep _)))

end PolishSpaceBook.SetTheoryModels
