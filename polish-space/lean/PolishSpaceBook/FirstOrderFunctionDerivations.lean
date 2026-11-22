module

public import PolishSpaceBook.FirstOrderFunctionEqualityRule
public import PolishSpaceBook.FirstOrderTheoryRules

@[expose] public section

/-!
# Translation of derivations under function elimination

The target theory contains the original sentence theory and the translated
finite assumptions. Special rules use the relational substitution and equality
lemmas; every eigenvariable remains fresh after adding sentence assumptions.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance functionDerivationsOldDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
local instance functionDerivationsNewDecidableEq :
    DecidableEq (AlphaFormula (L.sum (functionSymbols ι))) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

@[simp] theorem eliminate_falsum : D.eliminate falsum = falsum := rfl

/-- Translate the finite assumptions pointwise. -/
def eliminateContext (Γ : Context (L.sum (functionSymbols ι))) : Context L := Γ.image D.eliminate

@[simp] theorem eliminateContext_insert (Γ : Context (L.sum (functionSymbols ι)))
    (φ : AlphaFormula (L.sum (functionSymbols ι))) :
    D.eliminateContext (insert φ Γ) = insert (D.eliminate φ) (D.eliminateContext Γ) := by
  simp [eliminateContext]

theorem fv_eliminateContext_subset (Γ : Context (L.sum (functionSymbols ι))) :
    (D.eliminateContext Γ).fv ⊆ Γ.fv := by
  intro x hx
  obtain ⟨ψ,hψ,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hψ
  exact Context.mem_fv_of_mem hφ (D.fv_eliminate_subset φ hx)

/-- Old sentence axioms accompany the translated temporary assumptions. -/
def eliminateTheory (T : Set (AlphaFormula L)) (Γ : Context (L.sum (functionSymbols ι))) :
    Set (AlphaFormula L) := T ∪ (↑(D.eliminateContext Γ) : Set (AlphaFormula L))

@[simp] theorem eliminateTheory_insert (T : Set (AlphaFormula L))
    (Γ : Context (L.sum (functionSymbols ι))) (φ : AlphaFormula (L.sum (functionSymbols ι))) :
    D.eliminateTheory T (insert φ Γ) = insert (D.eliminate φ) (D.eliminateTheory T Γ) := by
  ext θ
  simp only [eliminateTheory,eliminateContext_insert,Set.mem_union,Finset.mem_coe,Finset.mem_insert,
    Set.mem_insert_iff]
  tauto

theorem not_free_eliminateTheory {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (Γ : Context (L.sum (functionSymbols ι))) (x : ℕ) (hx : x ∉ Γ.fv) :
    ∀ θ ∈ D.eliminateTheory T Γ, x ∉ θ.fv := by
  intro θ hθ hm
  rcases hθ with hθ | hθ
  · have he : θ.fv = ∅ := hT hθ
    exact Finset.notMem_empty x (he ▸ hm)
  · exact hx (D.fv_eliminateContext_subset Γ (Context.mem_fv_of_mem hθ hm))

/-- Every natural-deduction derivation translates, using the old theory for term values. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Proof translation for functions
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induct on the given natural-deduction derivation. Translate each finite context pointwise and add the old
    sentence theory. If translated subderivations use different finite subsets of that theory, take their union.
    Adding an assumption commutes with translation of contexts, so assumption discharge is preserved by the
    deduction lemma. A free variable of the translated context already occurred in the original context.
    The added sentence assumptions have no free variables.
    
    The connective rules, falsity elimination, and excluded middle retain their constructors. Universal introduction
    therefore retains its eigenvariable condition. For existential elimination, the original eigenvariable remains
    absent from the translated context, conclusion, and existential premise. The temporary body assumption is the
    required variable instance because translation commutes with variable substitution. For equality introduction,
    use \termuse{translated equality reflexivity}.
-/
theorem eliminate_derivation {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    {Γ : Context (L.sum (functionSymbols ι))} {φ : AlphaFormula (L.sum (functionSymbols ι))}
    (h : Derives Γ φ) : ProvesFrom (D.eliminateTheory T Γ) (D.eliminate φ) := by
  induction h with
  | hyp Γ φ =>
    rw [eliminateTheory_insert]
    exact ProvesFrom.hyp (Set.mem_insert _ _)
  | andIntro hφ hψ ihφ ihψ => simpa using ihφ.map₂ ihψ Derives.andIntro
  | andLeft h ih => exact ih.map (fun h => Derives.andLeft (by simpa using h))
  | andRight h ih => exact ih.map (fun h => Derives.andRight (by simpa using h))
  | orLeft ψ h ih => simpa using ih.map (Derives.orLeft (D.eliminate ψ))
  | orRight φ h ih => simpa using ih.map (Derives.orRight (D.eliminate φ))
  | orElim hd hl hr ihd ihl ihr =>
    exact ProvesFrom.orElim (by simpa using ihd) (by simpa using ihl) (by simpa using ihr)
  | impIntro h ih => simpa using ProvesFrom.deduction.mp (by simpa using ih)
  | impElim hf ha ihf iha => exact (by simpa using ihf : ProvesFrom _ (binary .imp _ _)).impElim iha
  | falseElim φ h ih => exact ih.map (fun h => Derives.falseElim _ (by simpa using h))
  | @allIntro Γ φ x h hx ih =>
    simpa using ProvesFrom.allIntro x (D.not_free_eliminateTheory hT Γ x hx) ih
  | allElim x φ t h ih =>
    exact ((D.proves_eliminate_allElim hT hu φ x t).mono Set.subset_union_left).impElim (by simpa [eliminateTheory] using ih)
  | exIntro x φ t h ih =>
    simpa [eliminateTheory] using ((D.proves_eliminate_exIntro hT hu φ x t).mono Set.subset_union_left).impElim ih
  | @exElim Γ x y φ χ he hc hy ihe ihc =>
    have hyΓ : y ∉ Γ.fv := fun hm => hy (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
    have hyχ : y ∉ (D.eliminate χ).fv := fun hm =>
      hy (Finset.mem_union_left _ (Finset.mem_union_right _ (D.fv_eliminate_subset χ hm)))
    have hyφ : y ∉ (quant .ex x (D.eliminate φ)).fv := by
      intro hm
      apply hy
      apply Finset.mem_union_right
      apply D.fv_eliminate_subset (quant .ex x φ)
      simpa using hm
    exact ProvesFrom.exElim x y (D.eliminate φ) (D.eliminate χ) (by simpa using ihe)
      (by simpa only [eliminateTheory_insert,eliminate_subst_var] using ihc)
      (D.not_free_eliminateTheory hT Γ y hyΓ) hyχ hyφ
  | eqIntro Γ t => exact (D.proves_eliminate_equal_refl hT hu t).mono Set.subset_union_left
  | eqElim φ x t r ht he iht ihe =>
    exact ((D.proves_eliminate_eqElim hT hu φ x t r).mono Set.subset_union_left).impElim
      (iht.map₂ ihe Derives.andIntro)
  | excludedMiddle Γ φ =>
    have h : ProvesFrom (D.eliminateTheory T Γ) (binary .disj (D.eliminate φ) (neg (D.eliminate φ))) :=
      ⟨∅,by simp,Derives.excludedMiddle ∅ (D.eliminate φ)⟩
    simpa [neg] using h

/-- Translation preserves finite proof support over arbitrary expanded-language assumptions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    All rules have now been translated. For an arbitrary theory of expanded-language assumptions, choose the finite
    support of its proof, apply the result just established, and include the translated support in the translated
    theory. No additional assumption on the free variables of the original hypotheses is needed.
-/
theorem eliminate_proof {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    {U : Set (AlphaFormula (L.sum (functionSymbols ι)))} {φ : AlphaFormula (L.sum (functionSymbols ι))}
    (h : ProvesFrom U φ) : ProvesFrom (T ∪ D.eliminate '' U) (D.eliminate φ) := by
  obtain ⟨Γ,hΓ,h⟩ := h
  apply (D.eliminate_derivation hT hu h).mono
  intro θ hθ
  rcases hθ with hθ | hθ
  · exact Or.inl hθ
  · obtain ⟨ψ,hψ,rfl⟩ := Finset.mem_image.mp hθ
    exact Or.inr ⟨ψ,hΓ ψ hψ,rfl⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
