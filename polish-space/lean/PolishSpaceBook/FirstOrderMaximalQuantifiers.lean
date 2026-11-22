module

public import PolishSpaceBook.FirstOrderQuantifierDuality

@[expose] public section

/-!
# Closed-instance clauses for quantifiers in a Henkin theory

Existential membership is witnessed by a closed constant term. Universal
membership is equivalent to membership of every closed instance: its converse
uses the syntactic quantifier duality and a Henkin witness for the negated body.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

@[simp] theorem namedClosedTerm_constant (c : L.Constants) :
    namedClosedTerm (c.term : L.Term Empty) = (c.term : L.Term ℕ) := by
  change Term.func c _ = Term.func c _
  exact congrArg (Term.func c) (Subsingleton.elim _ _)

theorem oneVariable_erase {φ : AlphaFormula L} {x : ℕ} (hφ : φ.fv ⊆ {x}) : φ.fv.erase x = ∅ :=
  (Finset.erase_eq_empty_iff _ _).mpr (Finset.subset_singleton_iff.mp hφ)

theorem oneVariable_quant_sentence (q : Quantifier) {φ : AlphaFormula L} {x : ℕ}
    (hφ : φ.fv ⊆ {x}) : quant q x φ ∈ Sentences L := by
  change (quant q x φ).fv = ∅
  simpa only [fv_quant] using oneVariable_erase hφ

theorem oneVariable_of_quant_sentence (q : Quantifier) {φ : AlphaFormula L} {x : ℕ}
    (hφ : quant q x φ ∈ Sentences L) : φ.fv ⊆ {x} :=
  Finset.subset_singleton_iff.mpr ((Finset.erase_eq_empty_iff _ _).mp (by simpa [Sentences] using hφ))

theorem oneVariable_subst_sentence {φ : AlphaFormula L} {x : ℕ} (hφ : φ.fv ⊆ {x}) (t : L.Term Empty) :
    φ.subst x (namedClosedTerm t) ∈ Sentences L := by
  change (φ.subst x (namedClosedTerm t)).fv = ∅
  simp only [fv_subst, fv_namedClosedTerm, ite_self, Finset.union_empty, oneVariable_erase hφ]

namespace MaximallyConsistent
variable {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
include hT

theorem ex_mem_iff (hH : HasHenkinWitnesses T) {φ : AlphaFormula L} {x : ℕ} (hφ : φ.fv ⊆ {x}) :
    quant .ex x φ ∈ T ↔ ∃ t : L.Term Empty, φ.subst x (namedClosedTerm t) ∈ T := by
  constructor
  · intro he
    obtain ⟨c, hc⟩ := hH x φ hφ
    refine ⟨c.term, hT.mem_of_proves (oneVariable_subst_sentence hφ _) ?_⟩
    simpa only [namedClosedTerm_constant] using (ProvesFrom.hyp hc).impElim (ProvesFrom.hyp he)
  · rintro ⟨t, ht⟩
    exact hT.mem_of_proves (oneVariable_quant_sentence .ex hφ)
      ((ProvesFrom.hyp ht).map (Derives.exIntro x φ (namedClosedTerm t)))

theorem all_mem_iff_no_ex_neg {φ : AlphaFormula L} {x : ℕ} (hφ : φ.fv ⊆ {x}) :
    quant .all x φ ∈ T ↔ quant .ex x (neg φ) ∉ T := by
  have hn : (neg φ).fv ⊆ {x} := by simpa using hφ
  exact (hT.mem_iff_proves (oneVariable_quant_sentence .all hφ)).trans
    ((ProvesFrom.all_iff_not_ex_not hT.sentences x φ).trans
      ((hT.mem_iff_proves (by simpa [Sentences] using oneVariable_quant_sentence .ex hn)).symm.trans
        (hT.neg_mem_iff (oneVariable_quant_sentence .ex hn))))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Suppose $\FreeVars{\varphi}\IncludedIn\{x\}$. The quantifier rules are
    $$\begin{aligned}
    (\existsbind{x}{\varphi})\in T^*&\iff
      \exists t\;\SubstFormula{\varphi}{x}{t}\in T^*,\\
    (\forallbind{x}{\varphi})\in T^*&\iff
      \forall t\;\SubstFormula{\varphi}{x}{t}\in T^*,
    \end{aligned}$$
    where $t$ ranges over closed $L_H$-terms. In the existential clause, the Henkin axiom and modus ponens give a
    constant witnessing membership; the converse is existential introduction. Universal elimination gives the forward
    direction of the universal clause.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Suppose every closed instance of $\varphi$ belongs to $T^*$.
    If $\existsbind{x}{\neg\varphi}\in T^*$, its Henkin witness gives the negation of one of these instances,
    contradicting consistency.
    Thus $\existsbind{x}{\neg\varphi}\notin T^*$, and the negation clause and this syntactic equivalence give
    $(\forallbind{x}{\varphi})\in T^*$.
-/
theorem all_mem_iff (hH : HasHenkinWitnesses T) {φ : AlphaFormula L} {x : ℕ} (hφ : φ.fv ⊆ {x}) :
    quant .all x φ ∈ T ↔ ∀ t : L.Term Empty, φ.subst x (namedClosedTerm t) ∈ T := by
  classical
  constructor
  · intro ha t
    exact hT.mem_of_proves (oneVariable_subst_sentence hφ t)
      ((ProvesFrom.hyp ha).map (Derives.allElim x φ (namedClosedTerm t)))
  · intro hi
    apply (hT.all_mem_iff_no_ex_neg hφ).mpr
    intro he
    have hn : (neg φ).fv ⊆ {x} := by simpa using hφ
    obtain ⟨t, ht⟩ := (hT.ex_mem_iff hH hn).mp he
    have hnot : neg (φ.subst x (namedClosedTerm t)) ∈ T := by simpa only [subst_neg] using ht
    exact hT.consistent.not_both (ProvesFrom.hyp (hi t)) (ProvesFrom.hyp hnot)

end MaximallyConsistent
end PolishSpaceBook.NamedFirstOrder
