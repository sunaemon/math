module

public import Mathlib.ModelTheory.Encoding
public import PolishSpaceBook.FirstOrderCompleteness
public import PolishSpaceBook.FirstOrderSyntaxCardinality

@[expose] public section

/-!
# Counting the Henkin languages and their actual quotient term model

The requests at each stage are a subset of variable/formula pairs. Their
constants are tagged by the natural-number stage. Finite syntax and a quotient
then give the bound on the model already constructed for completeness.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language Cardinal
universe u v
variable {L : Language.{u,v}}

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    A Henkin request consists of a variable and such a
    formula, subject to the free-variable condition, so there are at most $\alephNull\cdot\kappa=\kappa$ requests.
-/
theorem card_henkinRequest_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) :
    #(HenkinRequest L) ≤ κ := by
  have hi : Function.Injective (fun r : HenkinRequest L => (r.name, r.formula)) := by
    rintro ⟨x, φ, hφ⟩ ⟨y, ψ, hψ⟩ h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  apply (mk_le_of_injective hi).trans
  simp only [mk_prod, mk_nat, lift_aleph0, lift_uzero]
  exact (mul_le_mul' hκ (card_alphaFormula_le κ hκ hL)).trans (le_of_eq (mul_eq_self hκ))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Adding their constants gives $|L_{n+1}|\le\kappa+\kappa=\kappa$.
    Starting with $L_0=L$, induction therefore bounds all stage languages by $\kappa$.
-/
theorem card_henkinStage_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) (n : ℕ) :
    (henkinStage L n).card ≤ κ := by
  induction n with
  | zero => simpa [henkinStage, card_withConstants] using hL
  | succ n ih =>
    change ((henkinStage L n)[[HenkinRequest (henkinStage L n)]]).card ≤ κ
    rw [card_withConstants]
    simp only [lift_id]
    exact (add_le_add ih (card_henkinRequest_le κ hκ ih)).trans (le_of_eq (add_eq_self hκ))

theorem card_henkinLabels_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) :
    #(henkinLabels L) ≤ κ := by
  change #((n : ℕ) × HenkinRequest (henkinStage L n)) ≤ κ
  rw [mk_sigma]
  apply (sum_le_lift_mk_mul_iSup _).trans
  simp only [mk_nat, lift_aleph0]
  exact (mul_le_mul' hκ (ciSup_le' (fun n => card_henkinRequest_le κ hκ (card_henkinStage_le κ hκ hL n)))).trans
    (le_of_eq (mul_eq_self hκ))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The final added constants are tagged by their birth stage, so there are at most
    $\alephNull\cdot\kappa=\kappa$ of them. Together with the original symbols they form a language $L_H$ of size at
    most $\kappa$. Extending the Henkin theory to a maximal consistent theory adds no symbols.
-/
theorem card_henkinLanguage_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) :
    (henkinLanguage L).card ≤ κ := by
  rw [henkinLanguage, card_withConstants]
  simp only [lift_id]
  exact (add_le_add (card_henkinStage_le κ hκ hL 0) (card_henkinLabels_le κ hκ hL)).trans
    (le_of_eq (add_eq_self hκ))

/-- Taking classes of closed terms cannot increase their cardinality. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The closed $L_H$-terms are finite expressions, so there are at most $\kappa$ of them. Taking their classes modulo
    provable equality does not increase cardinality. Thus the term model has size at most $\kappa$.
-/
theorem card_termModel_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ)
    (T : Set (AlphaFormula L)) : lift.{v} #(TermModel T) ≤ κ := by
  have hfunc : lift.{v} #(Σ n, L.Functions n) ≤ κ := by
    unfold Language.card Language.Symbols at hL
    rw [mk_sum] at hL
    exact (le_add_of_nonneg_right zero_le).trans hL
  apply (lift_le.mpr mk_quotient_le).trans
  apply (lift_le.mpr (Term.card_le (L := L) (α := Empty))).trans
  simpa only [lift_max, lift_aleph0, mk_sum, mk_empty, lift_zero, zero_add, lift_lift, lift_uzero]
    using max_le hκ hfunc

/-- The reduct of the completeness proof's own term model meets the cardinal bound. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Cardinal bound for the Henkin model
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The truth lemma makes it a model of the extended theory; its reduct to $L$ has the same domain and satisfies $T$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *Set-sized convention.* "Model" always means \termdefine{set-sized}: the domain $M$ is a set, so quantifying over models
    stays within ZFC's class of sets — and the Henkin construction below shows this is no real restriction, since every
    consistent theory $T$ in a language $L$ has a model of size $\le \max(|L|, |T|, \alephNull)$. Readers working inside
    a fixed Grothendieck universe $U$ as in §{sec:inaccessible-universes} may read "set-sized" as "$U$-small" when
    the language and theory are $U$-small and the universe contains
    the set of natural numbers.
    Proper-class "models" such as the universe $V$ of §{sec:zfc-classes} are spoken of only informally, with satisfaction
    interpreted by relativizing formulas in the metatheory of §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Taking $\kappa=\max(|L|,|X|,\alephNull)$ gives the general downward bound. For a consistent $L$-theory,
    $\kappa=\max(|L|,\alephNull)$ already suffices. A separate factor for $|T|$ is unnecessary: a theory is a set of
    sentences, and the total number of $L$-sentences is at most this same bound.
-/
theorem Consistent.exists_model_card_le {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) :
    ∃ (M : Type (max u v)) (inst : L.Structure M), Nonempty M ∧
      (∀ (s : ℕ → M) ψ, ψ ∈ T → @AlphaFormula.Realize L M inst ψ s) ∧ #M ≤ κ := by
  obtain ⟨U, hU, hH, hsub⟩ := exists_maximalHenkinExtension hT hclosed
  obtain ⟨hne, hm⟩ := termModel_satisfies hU hH
  let f := henkinBaseInclusion L
  refine ⟨TermModel U, f.reduct (TermModel U), hne, ?_, ?_⟩
  · intro s ψ hψ
    exact (ψ.mapLanguage_realize_reduct f s).mp (hm s _ (hsub ⟨ψ, hψ, rfl⟩))
  · have hc := card_termModel_le κ hκ (card_henkinLanguage_le κ hκ hL) U
    rw [lift_id'.{v,u} #(TermModel U)] at hc
    exact hc

end PolishSpaceBook.NamedFirstOrder
