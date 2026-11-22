module

public import PolishSpaceBook.FirstOrderWeakening

@[expose] public section

/-!
# Finite support, deduction, and syntactic consistency

Hypothesis substitution follows by induction on the finite context, discharging
one assumption at a time. Theory consequences retain finite support throughout.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

namespace Derives

/-- Replace finitely many hypotheses by their derivations in another context. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    For the forward implication, choose the finite context used in the derivation, remove $\sigma$ from that context,
    and discharge it by implication introduction. The remaining context lies in $T$. For the reverse implication,
    use weakening to combine a finite derivation of the implication with the additional assumption, then apply
    modus ponens. To replace derived assumptions in a finite derivation, induct on their number: discharge one
    assumption by implication introduction, apply induction to the remaining assumptions, and apply modus ponens
    to a derivation of the discharged assumption. The empty case is weakening.
-/
theorem cut {Γ Δ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ)
    (hΓ : ∀ ψ ∈ Γ, Derives Δ ψ) : Derives Δ φ := by
  induction Γ using Finset.induction_on generalizing φ with
  | empty => exact h.weaken (Finset.empty_subset Δ)
  | @insert ψ Γ hψ ih =>
    have hf : Derives Δ (binary .imp ψ φ) :=
      ih (impIntro h) (fun A hA => hΓ A (Finset.mem_insert_of_mem hA))
    exact impElim hf (hΓ ψ (Finset.mem_insert_self _ _))

/-- Classical double-negation elimination, using exactly the printed LEM rule. -/
theorem doubleNegElim {Γ : Context L} {φ : AlphaFormula L} (h : Derives Γ (neg (neg φ))) :
    Derives Γ φ := by
  apply orElim (excludedMiddle Γ φ)
  · exact hyp Γ φ
  · apply falseElim φ
    exact impElim (h.weaken (Finset.subset_insert _ _)) (hyp Γ (neg φ))

/-- The classical antecedent consequence of a refuted implication. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the third consequence, deduction gives $T\vdash\neg(\sigma\to\tau)$.
    Under the additional assumption $\neg\sigma$, one derives $\sigma\to\tau$ by assuming $\sigma$, obtaining
    falsity, and using falsity elimination. This contradicts the negated implication, so double-negation elimination
    gives $T\vdash\sigma$. Under the additional assumption $\tau$, implication introduction again gives
    $\sigma\to\tau$, hence a contradiction; discharging this assumption gives $T\vdash\neg\tau$.
    \end{proof}
-/
theorem negImpLeft {Γ : Context L} {φ ψ : AlphaFormula L}
    (h : Derives Γ (neg (binary .imp φ ψ))) : Derives Γ φ := by
  apply doubleNegElim
  apply negIntro
  apply impElim (h.weaken (Finset.subset_insert _ _))
  apply impIntro
  apply falseElim ψ
  exact impElim (assumption (by simp [neg])) (hyp _ φ)

/-- The consequent of a refuted implication must itself be refutable. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the third consequence, deduction gives $T\vdash\neg(\sigma\to\tau)$.
    Under the additional assumption $\neg\sigma$, one derives $\sigma\to\tau$ by assuming $\sigma$, obtaining
    falsity, and using falsity elimination. This contradicts the negated implication, so double-negation elimination
    gives $T\vdash\sigma$. Under the additional assumption $\tau$, implication introduction again gives
    $\sigma\to\tau$, hence a contradiction; discharging this assumption gives $T\vdash\neg\tau$.
    \end{proof}
-/
theorem negImpRight {Γ : Context L} {φ ψ : AlphaFormula L}
    (h : Derives Γ (neg (binary .imp φ ψ))) : Derives Γ (neg ψ) := by
  apply negIntro
  apply impElim (h.weaken (Finset.subset_insert _ _))
  apply impIntro
  exact assumption (by simp)

end Derives
namespace ProvesFrom

theorem mono {T U : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (h : ProvesFrom T φ) (hTU : T ⊆ U) : ProvesFrom U φ := by
  obtain ⟨Γ, hΓ, h⟩ := h
  exact ⟨Γ, fun ψ hψ => hTU (hΓ ψ hψ), h⟩

theorem hyp {T : Set (AlphaFormula L)} {φ : AlphaFormula L} (hφ : φ ∈ T) : ProvesFrom T φ :=
  ⟨{φ}, by intro ψ hψ; simpa using (Finset.mem_singleton.mp hψ) ▸ hφ,
    Derives.assumption (Finset.mem_singleton_self _)⟩

/-- A uniform one-premise rule preserves finite support. -/
theorem map {T : Set (AlphaFormula L)} {φ ψ : AlphaFormula L} (h : ProvesFrom T φ)
    (f : ∀ {Γ}, Derives Γ φ → Derives Γ ψ) : ProvesFrom T ψ := by
  obtain ⟨Γ, hΓ, h⟩ := h
  exact ⟨Γ, hΓ, f h⟩

theorem impElim {T : Set (AlphaFormula L)} {φ ψ : AlphaFormula L}
    (hf : ProvesFrom T (binary .imp φ ψ)) (ha : ProvesFrom T φ) : ProvesFrom T ψ := by
  obtain ⟨Γ, hΓ, hf⟩ := hf
  obtain ⟨Δ, hΔ, ha⟩ := ha
  refine ⟨Γ ∪ Δ, ?_, .impElim (hf.weaken (Finset.subset_union_left))
    (ha.weaken (Finset.subset_union_right))⟩
  intro A hA
  exact (Finset.mem_union.mp hA).elim (hΓ A) (hΔ A)

/-- Discharge an axiom even when the theory is infinite. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    For the forward implication, choose the finite context used in the derivation, remove $\sigma$ from that context,
    and discharge it by implication introduction. The remaining context lies in $T$. For the reverse implication,
    use weakening to combine a finite derivation of the implication with the additional assumption, then apply
    modus ponens. To replace derived assumptions in a finite derivation, induct on their number: discharge one
    assumption by implication introduction, apply induction to the remaining assumptions, and apply modus ponens
    to a derivation of the discharged assumption. The empty case is weakening.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Deduction and consistency
-/
theorem deduction {T : Set (AlphaFormula L)} {φ ψ : AlphaFormula L} :
    ProvesFrom (insert φ T) ψ ↔ ProvesFrom T (binary .imp φ ψ) := by
  constructor
  · rintro ⟨Γ, hΓ, hd⟩
    refine ⟨Γ.erase φ, ?_, .impIntro (hd.weaken ?_)⟩
    · intro A hA
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hA
      exact (hΓ A hmem).resolve_left hne
    · intro A hA
      by_cases he : A = φ
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he, hA⟩)
  · intro h
    exact (h.mono (Set.subset_insert _ _)).impElim (hyp (Set.mem_insert _ _))

/-- A finite derivation can use previously derived theory consequences as assumptions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    For the forward implication, choose the finite context used in the derivation, remove $\sigma$ from that context,
    and discharge it by implication introduction. The remaining context lies in $T$. For the reverse implication,
    use weakening to combine a finite derivation of the implication with the additional assumption, then apply
    modus ponens. To replace derived assumptions in a finite derivation, induct on their number: discharge one
    assumption by implication introduction, apply induction to the remaining assumptions, and apply modus ponens
    to a derivation of the discharged assumption. The empty case is weakening.
-/
theorem of_derives {T : Set (AlphaFormula L)} {Γ : Context L} {φ : AlphaFormula L}
    (h : Derives Γ φ) (hΓ : ∀ ψ ∈ Γ, ProvesFrom T ψ) : ProvesFrom T φ := by
  induction Γ using Finset.induction_on generalizing φ with
  | empty => exact ⟨∅, by simp, h⟩
  | @insert ψ Γ hψ ih =>
    exact (ih (.impIntro h) (fun A hA => hΓ A (Finset.mem_insert_of_mem hA))).impElim
      (hΓ ψ (Finset.mem_insert_self _ _))

theorem cut {T U : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (h : ProvesFrom U φ) (hU : ∀ ψ ∈ U, ProvesFrom T ψ) : ProvesFrom T φ := by
  obtain ⟨Γ, hΓ, h⟩ := h
  exact of_derives h (fun ψ hψ => hU ψ (hΓ ψ hψ))

theorem doubleNegElim {T : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (h : ProvesFrom T (neg (neg φ))) : ProvesFrom T φ := h.map Derives.doubleNegElim

theorem negImpLeft {T : Set (AlphaFormula L)} {φ ψ : AlphaFormula L}
    (h : ProvesFrom T (neg (binary .imp φ ψ))) : ProvesFrom T φ := h.map Derives.negImpLeft

theorem negImpRight {T : Set (AlphaFormula L)} {φ ψ : AlphaFormula L}
    (h : ProvesFrom T (neg (binary .imp φ ψ))) : ProvesFrom T (neg ψ) := h.map Derives.negImpRight

end ProvesFrom

/-- Syntactic consistency; no model-existence assumption enters this definition. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a theory $T$, write $\ConsistentTheory{T}$ for the metatheoretic assertion that $T$ is syntactically consistent,
    meaning that $T\nvdash\bot$. The completeness theorem below will show that this is equivalent to having a model.
-/
def Consistent (T : Set (AlphaFormula L)) : Prop := ¬ProvesFrom T falsum

namespace Consistent

theorem mono {T U : Set (AlphaFormula L)} (hU : Consistent U) (hTU : T ⊆ U) : Consistent T :=
  fun h => hU (h.mono hTU)

theorem not_both {T : Set (AlphaFormula L)} (hT : Consistent T) {φ : AlphaFormula L}
    (hp : ProvesFrom T φ) (hn : ProvesFrom T (neg φ)) : False := hT (hn.impElim hp)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the first consequence, a contradiction after adjoining the sentence would yield its negation by deduction;
    modus ponens with its existing derivation contradicts consistency. For the second, a contradiction after adjoining
    the negation would yield the double negation of the sentence. Double-negation elimination follows by splitting
    into the sentence and its negation using LEM: the latter case contradicts the double negation, and falsity
    elimination finishes. This would contradict non-derivability.
-/
theorem insert_of_proves {T : Set (AlphaFormula L)} (hT : Consistent T) {φ : AlphaFormula L}
    (hφ : ProvesFrom T φ) : Consistent (insert φ T) := by
  intro h
  exact hT (ProvesFrom.deduction.mp h |>.impElim hφ)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the first consequence, a contradiction after adjoining the sentence would yield its negation by deduction;
    modus ponens with its existing derivation contradicts consistency. For the second, a contradiction after adjoining
    the negation would yield the double negation of the sentence. Double-negation elimination follows by splitting
    into the sentence and its negation using LEM: the latter case contradicts the double negation, and falsity
    elimination finishes. This would contradict non-derivability.
-/
theorem insert_neg_of_not_proves {T : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (hφ : ¬ProvesFrom T φ) : Consistent (insert (neg φ) T) := by
  intro h
  exact hφ (ProvesFrom.doubleNegElim (ProvesFrom.deduction.mp h))

end Consistent

/-- Failure to adjoin a sentence yields a proof of its negation. -/
theorem not_consistent_insert_iff {T : Set (AlphaFormula L)} {φ : AlphaFormula L} :
    ¬Consistent (insert φ T) ↔ ProvesFrom T (neg φ) := by
  classical
  simp only [Consistent, not_not, neg, ProvesFrom.deduction]

end PolishSpaceBook.NamedFirstOrder
