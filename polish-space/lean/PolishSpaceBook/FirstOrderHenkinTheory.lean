module

public import PolishSpaceBook.FirstOrderHenkinFiniteStage

@[expose] public section

/-!
# A consistent theory with all Henkin witnesses

The limit contains the initial theory and a witness axiom for every formula
whose free variables lie in one specified variable. Every final formula comes
from a finite stage, so its witness is present at the next stage.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

/-- Every one-variable formula has a named witness axiom in the theory. -/
def HasHenkinWitnesses (T : Set (AlphaFormula L)) : Prop :=
  ∀ (x : ℕ) (φ : AlphaFormula L), φ.fv ⊆ {x} →
    ∃ c : L.Constants, binary .imp (quant .ex x φ) (φ.subst x c.term) ∈ T

theorem HasHenkinWitnesses.mono {T U : Set (AlphaFormula L)} (hT : HasHenkinWitnesses T) (hTU : T ⊆ U) :
    HasHenkinWitnesses U := by
  intro x φ hφ
  obtain ⟨c, hc⟩ := hT x φ hφ
  exact ⟨c, hTU hc⟩

@[simp] theorem henkinInclusion_newConstant (n : ℕ) (r : HenkinRequest (henkinStage L n)) :
    (henkinInclusion L (n + 1)).onTerm ((henkinStage L n).con r).term =
      (((henkinStage L 0).con (⟨n, r⟩ : henkinLabels L)).term : (henkinLanguage L).Term ℕ) := by
  simp [Constants.term, Language.con, LHom.onTerm, henkinInclusion, LHom.sumElim, constantsToSymbols]
  exact congrArg (Term.func _) (Subsingleton.elim _ _)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Every $L_H$-formula belongs to some finite stage. Each symbol was introduced at a finite stage, and each term
    and formula uses only finitely many symbols. More explicitly, mapping to a sufficiently late stage by the
    preceding symbol map and then including back fixes every symbol occurring in the formula. Induction on terms
    and formulas shows that this round trip fixes the formula itself; the same holds for its $\alpha$-class.
    Thus an $L_H$-formula with free variables among $x$ is an $L_n$-formula for some $n$, and its Henkin axiom
    belongs to $T_{n+1}\IncludedIn S$. The construction also shows $T\IncludedIn S$.
    \end{proof}
-/
theorem henkinLimitTheory_witnesses (T : Set (AlphaFormula L)) : HasHenkinWitnesses (henkinLimitTheory T) := by
  intro x φ hφ
  obtain ⟨n, ψ, hψ⟩ := exists_henkinStage_formula L φ
  have hfree : ψ.fv ⊆ {x} := by rw [← hψ, fv_mapLanguage] at hφ; exact hφ
  let r : HenkinRequest (henkinStage L (n + 1)) := ⟨x, ψ, hfree⟩
  refine ⟨(henkinStage L 0).con (⟨n + 1, r⟩ : henkinLabels L), ?_⟩
  have hw := henkinImageTheory_subset_limit T (n + 2)
    ⟨henkinAxiom r x ψ, henkinStageTheory_witness T (n + 1) r, rfl⟩
  have hc := henkinInclusion_step L (n + 1)
  change (henkinInclusion L (n + 2)).comp ((henkinStage L (n + 1)).lhomWithConstants _) = _ at hc
  unfold henkinAxiom at hw
  erw [mapLanguage_binary, mapLanguage_quant, mapLanguage_subst] at hw
  erw [mapLanguage_comp, hc, hψ] at hw
  erw [henkinInclusion_newConstant] at hw
  exact hw


/-- The original language embeds into the final language. -/
def henkinBaseInclusion (L : Language.{u,v}) : L →ᴸ henkinLanguage L :=
  (henkinInclusion L 0).comp (L.lhomWithConstants _)

theorem henkinBaseInclusion_injective : (henkinBaseInclusion L).Injective where
  onFunction := fun h => Sum.inl.inj (Sum.inl.inj h)
  onRelation := fun h => Sum.inl.inj (Sum.inl.inj h)

theorem henkinLimitTheory_extends (T : Set (AlphaFormula L)) :
    AlphaFormula.mapLanguage (henkinBaseInclusion L) '' T ⊆ henkinLimitTheory T := by
  rintro _ ⟨φ, hφ, rfl⟩
  apply henkinImageTheory_subset_limit T 0
  exact ⟨φ.mapLanguage (L.lhomWithConstants _), ⟨φ, hφ, rfl⟩, mapLanguage_comp _ _ _⟩

/-- The syntactic Henkin construction, before taking a maximal consistent extension. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Henkin extension
-/
theorem consistent_henkin_extension {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) :
    Consistent (henkinLimitTheory T) ∧ henkinLimitTheory T ⊆ Sentences (henkinLanguage L) ∧
      HasHenkinWitnesses (henkinLimitTheory T) ∧
      AlphaFormula.mapLanguage (henkinBaseInclusion L) '' T ⊆ henkinLimitTheory T :=
  ⟨hT.henkinLimitTheory hclosed, henkinLimitTheory_sentences hclosed,
    henkinLimitTheory_witnesses T, henkinLimitTheory_extends T⟩

/-- Maximizing the Henkin theory retains every named witness. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The \termuse{Lindenbaum extension lemma} gives a maximal consistent extension $T^*\supseteq S$ in $L_H$.
    It is deductively closed and decides every sentence. Since it contains $S$, it retains all Henkin witnesses.
-/
theorem exists_maximalHenkinExtension {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) :
    ∃ U : Set (AlphaFormula (henkinLanguage L)), MaximallyConsistent U ∧ HasHenkinWitnesses U ∧
      AlphaFormula.mapLanguage (henkinBaseInclusion L) '' T ⊆ U := by
  obtain ⟨U, hSU, hU⟩ := exists_maximallyConsistent (hT.henkinLimitTheory hclosed)
    (henkinLimitTheory_sentences hclosed)
  exact ⟨U, hU, (henkinLimitTheory_witnesses T).mono hSU, Set.Subset.trans (henkinLimitTheory_extends T) hSU⟩

end PolishSpaceBook.NamedFirstOrder
