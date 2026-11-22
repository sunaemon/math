module

public import PolishSpaceBook.FirstOrderConstantElimination

@[expose] public section

/-!
# Consistency of adjoining one fresh Henkin witness

A refuted witness implication yields its existential antecedent and the negation
of its constant instance. Constant elimination turns the latter into a variable
instance; existential elimination contradicts the old theory's consistency.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula Filter
universe u v w
variable {L : Language.{u,v}} {A : Type w}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

namespace ProvesFrom

/-- The existential premise contradicts a uniformly refuted variable instance. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Combine the finite sets of axioms used in these two derivations and apply weakening to use the same context.
    Under the additional assumption $\psi\subst{x}{y}$, modus ponens gives falsity.
    Existential elimination now gives $T\vdash\bot$. Its side condition holds because the theory consists of
    sentences, the existential premise is closed, and falsity has no free variables. This contradicts consistency.
    \end{proof}
-/
theorem falsum_of_ex_neg_instance {T : Set (AlphaFormula L)} (hclosed : T ⊆ Sentences L)
    (φ : AlphaFormula L) (x y : ℕ) (hφ : φ.fv ⊆ {x})
    (he : ProvesFrom T (quant .ex x φ)) (hn : ProvesFrom T (neg (φ.subst x (.var y)))) :
    ProvesFrom T falsum := by
  obtain ⟨Γ, hΓ, he⟩ := he
  obtain ⟨Δ, hΔ, hn⟩ := hn
  have hΘ : ∀ ψ ∈ Γ ∪ Δ, ψ ∈ T := by
    intro ψ hψ
    exact (Finset.mem_union.mp hψ).elim (hΓ ψ) (hΔ ψ)
  have hFV : (Γ ∪ Δ).fv = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨ψ, hψ, hz⟩ := Finset.mem_biUnion.mp hz
    have hψFV : ψ.fv = ∅ := hclosed (hΘ ψ hψ)
    simp [hψFV] at hz
  have hExFV : (quant .ex x φ).fv = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [fv_quant] at hz
    obtain ⟨hzx, hz⟩ := Finset.mem_erase.mp hz
    exact hzx (Finset.mem_singleton.mp (hφ hz))
  refine ⟨Γ ∪ Δ, hΘ, .exElim x y φ falsum (he.weaken Finset.subset_union_left) ?_ ?_⟩
  · exact .impElim ((hn.weaken Finset.subset_union_right).weaken (Finset.subset_insert _ _))
      (.hyp _ (φ.subst x (.var y)))
  · simp [hFV, hExFV]

end ProvesFrom

/-- Any one fresh witness axiom can be adjoined in the extended language. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: One fresh Henkin witness
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    If the new axiom caused a contradiction, the \termuse{first-order deduction and consistency lemma} would give
    $T\vdash\existsbind{x}{\psi}$ and $T\vdash\neg(\psi\subst{x}{c})$ in the expanded language.
    The \termuse{constant extension lemma} brings the first derivation back to the original language.
    In the second derivation, replace the added constants by a sufficiently fresh variable $y\ne x$ as in that
    lemma's proof. Commutation with substitution gives $T\vdash\neg(\psi\subst{x}{y})$ in the original language.
-/
theorem Consistent.adjoin_henkinAxiom {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) (a : A) (x : ℕ) (φ : AlphaFormula L) (hφ : φ.fv ⊆ {x}) :
    Consistent (insert (henkinAxiom a x φ) (AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T)) := by
  intro hbad
  have hn := ProvesFrom.deduction.mp hbad
  have he : ProvesFrom (AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T)
      (quant .ex x (φ.mapLanguage (L.lhomWithConstants A))) := ProvesFrom.negImpLeft hn
  have hi : ProvesFrom (AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T)
      (neg ((φ.mapLanguage (L.lhomWithConstants A)).subst x (L.con a).term)) := ProvesFrom.negImpRight hn
  have he' : ProvesFrom T (quant .ex x φ) :=
    (ProvesFrom.withConstants_iff T (quant .ex x φ)).mp (by simpa using he)
  obtain ⟨y, hy, hyx⟩ := (hi.dropConstants_eventually.and (eventually_gt_atTop x)).exists
  have hni : ProvesFrom T (neg (φ.subst x (.var y))) := by
    simpa [neg, dropConstants_subst, ne_of_gt hyx, Constants.term, Language.con] using hy
  exact hT (ProvesFrom.falsum_of_ex_neg_instance hclosed φ x y hφ he' hni)

end PolishSpaceBook.NamedFirstOrder
