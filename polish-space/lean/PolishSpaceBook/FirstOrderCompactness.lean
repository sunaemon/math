module

public import PolishSpaceBook.FirstOrderCompleteness

@[expose] public section

/-!
# Compactness from completeness and finite derivations

If a sentence theory had no model, completeness would give a finite derivation
of falsity. A model of the finite context in that derivation contradicts
soundness. Finite-fragment consistency also follows directly from proof support.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w
variable {L : Language.{u,v}}

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: compactness theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] If $T$ had no model, then $T \vDash \bot$ vacuously, so by Gödel completeness the sentence $\bot$
    would be derivable from $T$. A formal proof is finite, so it uses only finitely many axioms $\sigma_1,\ldots,\sigma_n$
    from $T$. Hence the finite theory $\{\sigma_1,\ldots,\sigma_n\}$ would prove $\bot$, and soundness would imply that it
    has no model. This contradicts the finite satisfiability hypothesis.
    \end{proof}
-/
theorem compactness {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hfinite : ∀ Γ : Context L, (∀ ψ ∈ Γ, ψ ∈ T) →
      ∃ (M : Type w) (inst : L.Structure M), Nonempty M ∧
        ∀ (s : ℕ → M) ψ, ψ ∈ Γ → @AlphaFormula.Realize L M inst ψ s) :
    ∃ (M : Type (max u v)) (inst : L.Structure M), Nonempty M ∧
      ∀ (s : ℕ → M) ψ, ψ ∈ T → @AlphaFormula.Realize L M inst ψ s := by
  by_contra hn
  have hbad : ProvesFrom T falsum := by
    by_contra hc
    exact hn (Consistent.exists_model hc hT)
  obtain ⟨Γ, hΓ, hd⟩ := hbad
  obtain ⟨M, inst, hne, hm⟩ := hfinite Γ hΓ
  let := inst
  let s : ℕ → M := fun _ => Classical.choice hne
  exact realize_falsum s (hd.sound s (hm s))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Equivalently, a theory is consistent iff every finite fragment is consistent. This is the form used behind the forcing
    convention of working with "a sufficiently large finite fragment of ZFC": compactness lets finite-fragment consistency
    be checked one fragment at a time, while downward Löwenheim--Skolem and Mostowski collapse then turn suitable transitive
    models into countable transitive ones.
-/
theorem consistent_iff_finite {T : Set (AlphaFormula L)} :
    Consistent T ↔ ∀ Γ : Context L, (∀ ψ ∈ Γ, ψ ∈ T) → Consistent (Γ : Set (AlphaFormula L)) := by
  constructor
  · intro hT Γ hΓ
    exact hT.mono hΓ
  · intro hfinite hbad
    obtain ⟨Γ, hΓ, hd⟩ := hbad
    exact hfinite Γ hΓ ⟨Γ, fun _ h => h, hd⟩

end PolishSpaceBook.NamedFirstOrder
