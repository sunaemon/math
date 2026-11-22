module

public import PolishSpaceBook.FirstOrderFunctionVariableSubstitution

@[expose] public section

/-!
# Equality reflexivity after function elimination

Open one graph value for the term and use it for both translated arguments.
The two existential introductions are justified by capture-avoiding variable
substitution; the temporary value is absent from the final translated equality.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Translated reflexive equality has a proof in the original theory, for every expanded-language term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: corollary
  title: Translated equality reflexivity
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Choose the starting index $B$ used in translating the equality, so its two argument witnesses are
    $v_B,v_{B+1}$. Put $w=v_{B+2}$ and $C=B+3$.
    The existence lemma gives $T\vdash\exists w\,\FirstOrderTermGraph{t}{w}{C}$.
    Temporarily assume the graph at this value. Substitute this same value for both argument witnesses in the
    translated equality. The preceding lemma identifies each instantiated argument graph with the assumed graph,
    up to $\alpha$-equivalence. Reflexivity proves equality of the two values, and the empty conjunction is true.
    Conjunction introduction and the two existential introductions therefore prove the translated equality under
    the temporary graph assumption. The variable $w$ is absent from the original term, hence is not free in the
    translation by its free-variable bound. It is also not free in the sentence assumptions. Existential elimination
    using the
    existence proof therefore discharges the temporary graph assumption and yields the required proof in $T$.
-/
theorem proves_eliminate_equal_refl {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t : (L.sum (functionSymbols ι)).Term ℕ) : ProvesFrom T (D.eliminate (equal t t)) := by
  let B := valueBound ![t,t]
  let w := B+2
  let C := w+1
  let ρ₀ := D.termGraph t B (B+2)
  let ρ₁ := D.termGraph t (B+1) (B+2)
  let ρ := D.termGraph t w C
  let A := binary .conj (binary .conj ρ₀ (binary .conj ρ₁ (binary .imp falsum falsum)))
    (equal (.var B) (.var (B+1)))
  let E := quant .ex (B+1) (quant .ex B A)
  change ProvesFrom T E
  have ht (a : ℕ) (ha : a ∈ t.varFinset) : a < B := valueBound_spec ![t,t] 0 a ha
  have hnot (a : ℕ) (ha : B ≤ a) : a ∉ t.varFinset := fun hm => by have := ht a hm; omega
  have hs (a : ℕ) (ha : B ≤ a) : termSubst t a (.var w) = t :=
    termSubst_not_free t a (.var w) (hnot a ha)
  have h₀ : ρ₀.subst B (.var w) = ρ := by
    have hh := D.termGraph_subst_var t B B w (B+2) C (by omega)
      (fun a ha => by have := ht a ha; omega) (by simp [C])
      (by rw [hs B (by omega)]; intro a ha; have := ht a ha; dsimp [C,w]; omega)
    simpa only [ρ₀,ρ,ite_true,hs B (by omega)] using hh
  have h₁ : ρ₁.subst (B+1) (.var w) = ρ := by
    have hh := D.termGraph_subst_var t (B+1) (B+1) w (B+2) C (by omega)
      (fun a ha => by have := ht a ha; omega) (by simp [C])
      (by rw [hs (B+1) (by omega)]; intro a ha; have := ht a ha; dsimp [C,w]; omega)
    simpa only [ρ₁,ρ,ite_true,hs (B+1) (by omega)] using hh
  have h₀free : B+1 ∉ ρ₀.fv := by
    intro hm
    rcases Finset.mem_insert.mp (D.fv_termGraph_subset t B (B+2) hm) with he | hm
    · omega
    · exact hnot (B+1) (by omega) hm
  have hρfree : B ∉ ρ.fv := by
    intro hm
    rcases Finset.mem_insert.mp (D.fv_termGraph_subset t w C hm) with he | hm
    · dsimp [w] at he; omega
    · exact hnot B (by omega) hm
  have he := D.proves_termGraph_exists hT hu t w C (by dsimp [C]; omega)
    (hnot w (by dsimp [w]; omega)) (fun a ha => by have := ht a ha; dsimp [C,w]; omega)
  obtain ⟨Γ,hΓ,he⟩ := he
  have hbody : Derives (insert ρ Γ) E := by
    have hA : Derives (insert ρ Γ) ((A.subst (B+1) (.var w)).subst B (.var w)) := by
      simp only [A, subst_binary, subst_falsum, subst_equal, subst_absent ρ₀ (B+1) (.var w) h₀free,
        h₁, h₀, subst_absent ρ B (.var w) hρfree]
      have hBw : B ≠ w := by dsimp [w]; omega
      have hB : B ≠ B+1 := by omega
      simp only [termSubst, Term.subst, ite_eq_right hB, ite_true, ite_eq_right (Ne.symm hBw)]
      exact .andIntro (.andIntro (.hyp Γ ρ) (.andIntro (.hyp Γ ρ) (.impIntro (.hyp _ falsum))))
        (.eqIntro (insert ρ Γ) (.var w))
    have hi : Derives (insert ρ Γ) (quant .ex B (A.subst (B+1) (.var w))) :=
      .exIntro B _ (.var w) hA
    apply Derives.exIntro (B+1) _ (.var w)
    simpa only [subst_quant_fresh .ex B A (B+1) (.var w) (by omega)
      (by simp only [Term.varFinset, Finset.mem_singleton]; dsimp [w]; omega)] using hi
  have hwE : w ∉ E.fv := by
    intro hm
    have ht' := D.fv_eliminate_subset (equal t t) hm
    change w ∈ t.varFinset ∪ t.varFinset at ht'
    exact hnot w (by dsimp [w]; omega) ((Finset.mem_union.mp ht').elim id id)
  refine ⟨Γ,hΓ,Derives.exElim w w ρ E he (by simpa only [subst_self] using hbody) ?_⟩
  have hwΓ : w ∉ Γ.fv := by rw [Context.fv_eq_empty_of_sentences hT Γ hΓ]; simp
  simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
    false_and, or_false, not_or]
  exact ⟨hwΓ,hwE⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
