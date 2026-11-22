module

public import PolishSpaceBook.SetTheoryGrothendieckModels
public import PolishSpaceBook.FirstOrderBoundedToNamed

@[expose] public section

/-! # Inaccessible models and syntactic consistency of the actual translated ZFC axioms -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas NamedFirstOrder
universe u w

/-- The literal full ZFC axioms translated into the book's named natural-deduction syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The existence of an inaccessible $\kappa$ implies that $V_\kappa$ is a transitive model of ZFC, hence implies
    $\mathrm{Con}(\mathrm{ZFC})$.
-/
def namedFullZFCTheory : Set (AlphaFormula membershipLanguage) :=
  (fun φ => AlphaFormula.mk (boundedToNamed φ)) '' fullZFCTheory

/-- Every translated axiom is still a sentence. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The existence of an inaccessible $\kappa$ implies that $V_\kappa$ is a transitive model of ZFC, hence implies
    $\mathrm{Con}(\mathrm{ZFC})$.
-/
theorem namedFullZFCTheory_sentences {ψ : AlphaFormula membershipLanguage}
    (hψ : ψ ∈ namedFullZFCTheory) : ψ.fv = ∅ := by
  obtain ⟨φ, _, rfl⟩ := hψ
  exact boundedToNamed_sentence φ

/-- Actual model truth supplies every translated axiom under every assignment. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The existence of an inaccessible $\kappa$ implies that $V_\kappa$ is a transitive model of ZFC, hence implies
    $\mathrm{Con}(\mathrm{ZFC})$.
-/
theorem namedFullZFCTheory_realize {M : Type w} [membershipLanguage.Structure M]
    (hM : M ⊨ fullZFCTheory) (s : ℕ → M) {ψ : AlphaFormula membershipLanguage}
    (hψ : ψ ∈ namedFullZFCTheory) : ψ.Realize s := by
  obtain ⟨φ, hφ, rfl⟩ := hψ
  exact (realize_boundedToNamed_sentence φ s).mpr (hM.realize_of_mem φ hφ)

/-- Soundness of the book's actual derivation rules forbids a derivation of falsity. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The existence of an inaccessible $\kappa$ implies that $V_\kappa$ is a transitive model of ZFC, hence implies
    $\mathrm{Con}(\mathrm{ZFC})$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    such an assertion implies $\mathrm{Con}(\mathrm{ZFC})$.
-/
theorem namedFullZFCTheory_consistent_of_model {M : Type w}
    [membershipLanguage.Structure M] [Nonempty M] (hM : M ⊨ fullZFCTheory) :
    NamedFirstOrder.Consistent namedFullZFCTheory :=
  not_proves_falsum_of_model (fun s _ hψ => namedFullZFCTheory_realize hM s hψ)

/-- An inaccessible cardinal yields syntactic consistency, not merely semantic satisfiability. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The existence of an inaccessible $\kappa$ implies that $V_\kappa$ is a transitive model of ZFC, hence implies
    $\mathrm{Con}(\mathrm{ZFC})$.
-/
theorem inaccessible_implies_namedZFC_consistent {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    NamedFirstOrder.Consistent namedFullZFCTheory := by
  have hU := inaccessible_vonNeumann_isGrothendieckUniverse hκ
  let : Nonempty (ZFSet.vonNeumann κ.ord) := ⟨⟨Ordinal.omega0.toZFSet, hU.omega_mem⟩⟩
  exact namedFullZFCTheory_consistent_of_model hU.models_fullZFC

end PolishSpaceBook.SetTheoryModels
