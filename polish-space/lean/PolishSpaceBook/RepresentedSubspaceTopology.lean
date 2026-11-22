module

public import PolishSpaceBook.RepresentedSubspaces

@[expose] public section

/-!
# Admissibility and the topology of represented subspaces

A continuous partial map into a subspace is first lifted into the original
name domain. Its represented values force the lift into the restricted domain.
Topology recovery then applies whenever the subspace is sequential.
-/
namespace PolishSpaceBook
open Set Function Topology
universe u
variable {X : Type u} [TopologicalSpace X]

omit [TopologicalSpace X] in
/-- The restricted domain retains the subspace topology on exactly the same names. -/
theorem continuous_restrictionOriginalName (δ : Representation X) (A : Set X) :
    Continuous (restrictionOriginalName δ A) :=
  continuous_subtype_val.subtype_mk _

/-- Restricting a continuous representation gives a continuous map to the subspace. -/
theorem Representation.IsContinuous.restrict {δ : Representation X}
    (hδ : δ.IsContinuous) (A : Set X) : (restrictedRepresentation δ A).IsContinuous :=
  (hδ.comp (continuous_restrictionOriginalName δ A)).subtype_mk _

/-- Lift into the original representation, then corestrict the lift using its values. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Admissible represented subspaces
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The restriction is continuous as a map into the subspace. To prove admissibility, take a continuous partial map $g:E\to A$, where $E\IncludedIn\BaireSpace$. Composing with the inclusion into $X$ and using the partial-map characterization of admissibility gives a continuous $H:E\to\DomainOf{\delta_X}$ such that $\delta_X(H(p))=g(p)$, with the right-hand side regarded as a point of $X$. Every value of $H$ therefore belongs to $\DomainOf{\delta_A}$. Corestricting $H$ to this domain preserves continuity and gives a lift of $g$ through $\delta_A$. This proves admissibility without any assumption on $A$.
-/
theorem Representation.IsAdmissible.restrict {δ : Representation X}
    (hδ : δ.IsAdmissible) (A : Set X) : (restrictedRepresentation δ A).IsAdmissible := by
  apply (admissible_iff_partial_lifting _).mpr
  refine ⟨hδ.1.restrict A, ?_⟩
  intro E g hg
  obtain ⟨H, hH, heq⟩ := (admissible_iff_partial_lifting δ).mp hδ |>.2 E
    (fun p => (g p).val) (continuous_subtype_val.comp hg)
  let F : E → (restrictedRepresentation δ A).domain := fun p =>
    ⟨(H p).val, (H p).property, (heq p).symm ▸ (g p).property⟩
  refine ⟨F, (continuous_subtype_val.comp hH).subtype_mk _, ?_⟩
  intro p
  exact Subtype.ext (heq p)

/-- Sequentiality is required of the subspace, not merely of the ambient space. -/
theorem isQuotientMap_restrictedRepresentation (δ : Representation X)
    (hδ : δ.IsAdmissible) (A : Set X) [SequentialSpace A] :
    IsQuotientMap (restrictedRepresentation δ A).toFun :=
  isQuotientMap_of_admissible _ (hδ.restrict A)

/-- The topology induced by the restricted names is exactly the ordinary subspace topology. -/
theorem restrictedRepresentation_isOpen_iff (δ : Representation X)
    (hδ : δ.IsAdmissible) (A : Set X) [SequentialSpace A] (U : Set A) :
    IsOpen U ↔ IsOpen ((restrictedRepresentation δ A).toFun ⁻¹' U) :=
  (isQuotientMap_restrictedRepresentation δ hδ A).isOpen_preimage.symm

/-- Metrizability is needed only for the subspace. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Admissible represented subspaces
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For the topology assertion, apply the convergent-sequence argument for topology recovery in
    §{sec:kreitz-weihrauch-admissibility}; that argument uses metrizability and admissibility, but not completeness. More
    explicitly, suppose $\delta_A^{-1}(U)$ is open and $U$ is not. Metrizability gives $x\in U$ and a sequence
    $\Sequence{x_n}{n\in\omega}$ in $\SetDifference{A}{U}$ converging to $x$. Let $e_\infty$ be the zero name and let $e_n$
    have a single one at coordinate $n$. On $E=\{e_\infty\}\cup\{e_n:n\in\NN\}$, the map sending $e_\infty$ to $x$ and $e_n$
    to $x_n$ is continuous. Admissibility lifts it continuously to the restricted name domain. Pulling back the open set
    $\delta_A^{-1}(U)$ along this lift makes $\{e_\infty\}$ open in $E$, contradicting $e_n\to e_\infty$. The other
    implication follows from continuity. The empty subspace satisfies the assertion trivially, and every subspace of a
    metrizable space is metrizable.
-/
theorem restrictedRepresentation_isOpen_iff_metrizable_subspace
    (δ : Representation X) (hδ : δ.IsAdmissible) (A : Set X)
    [TopologicalSpace.MetrizableSpace A] (U : Set A) :
    IsOpen U ↔ IsOpen ((restrictedRepresentation δ A).toFun ⁻¹' U) :=
  restrictedRepresentation_isOpen_iff δ hδ A U

/-- Every metrizable subspace satisfies the sequentiality hypothesis. -/
theorem restrictedRepresentation_isOpen_iff_metrizable [TopologicalSpace.MetrizableSpace X]
    (δ : Representation X) (hδ : δ.IsAdmissible) (A : Set X) (U : Set A) :
    IsOpen U ↔ IsOpen ((restrictedRepresentation δ A).toFun ⁻¹' U) :=
  restrictedRepresentation_isOpen_iff δ hδ A U

end PolishSpaceBook
