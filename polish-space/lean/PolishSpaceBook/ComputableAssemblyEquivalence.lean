module

public import PolishSpaceBook.LambdaComputablePointAssemblies
public import PolishSpaceBook.ComputableRepresentationEquivalence

@[expose] public section

namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory
universe u

/-- Translators of names in both directions give inverse tracked maps on the
computable points, even when the translated names are not literally inverse. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    §{sec:domains-tte-equivalence} proves continuous equivalence between Cauchy-name streams and domain chains.
    It does not assert a computable equivalence for arbitrary presentations. If computable translators in both
    directions are additionally supplied, the induced index transformations give inverse assembly morphisms on
    computable points and hence isomorphic objects in $\EffCat$. Mere Scott continuity or topological admissibility
    does not supply those translators.
-/
def computablePointRepresentationIso {X : Type u} {δ ε : Representation X}
    (h : ComputablyEquivalent δ ε) : computablePointAssembly δ ≅ computablePointAssembly ε where
  hom := computablePointMap h.1
  inv := computablePointMap h.2
  hom_inv_id := by
    apply Assembly.Hom.ext
    intro x
    exact Subtype.ext rfl
  inv_hom_id := by
    apply Assembly.Hom.ext
    intro x
    exact Subtype.ext rfl

/-- The assembly embedding carries the same explicit isomorphism into the PER category. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    §{sec:domains-tte-equivalence} proves continuous equivalence between Cauchy-name streams and domain chains.
    It does not assert a computable equivalence for arbitrary presentations. If computable translators in both
    directions are additionally supplied, the induced index transformations give inverse assembly morphisms on
    computable points and hence isomorphic objects in $\EffCat$. Mere Scott continuity or topological admissibility
    does not supply those translators.
-/
def embeddedComputablePointRepresentationIso {X : Type u} {δ ε : Representation X}
    (h : ComputablyEquivalent δ ε) :
    Assembly.embedding.obj (computablePointAssembly δ) ≅
      Assembly.embedding.obj (computablePointAssembly ε) :=
  Assembly.embedding.mapIso (computablePointRepresentationIso h)

/-- The canonical fiberwise existential, with PER existence evidence included,
contains pairs of realizers; its base witness remains semantic data. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    *   a proof of $\varphi\land\psi$ is a pair of realizers;
    *   a proof of $\varphi\lor\psi$ is a tag and a realizer for the chosen side;
    *   a proof of $\varphi\to\psi$ is an index transforming realizers of $\varphi$ into realizers of $\psi$;
    *   a realizer of $\exists x\,\varphi(x)$ lies in the union of the realizer sets over possible witnesses,
        with existence evidence included when quantifying over a PER object. It need not encode an arbitrary
        base-set witness as a natural number.
-/
theorem per_exists_mem_iff (X : RealizerPER.{u}) (φ : X.Carrier → Set ℕ) (n : ℕ) :
    n ∈ realizabilityExists (fun _ : X.Carrier => ()) (realizabilityAnd X.extent φ) () ↔
      ∃ x a, a ∈ X.extent x ∧ ∃ b, b ∈ φ x ∧ n = Nat.pair a b := by
  constructor
  · rintro ⟨x, _, hx⟩
    obtain ⟨a, ha, b, hb, he⟩ := (realizabilityAnd_mem_iff X.extent φ x n).mp hx
    exact ⟨x, a, ha, b, hb, he⟩
  · rintro ⟨x, a, ha, b, hb, he⟩
    exact ⟨x, rfl, (realizabilityAnd_mem_iff X.extent φ x n).mpr ⟨a, ha, b, hb, he⟩⟩

end PolishSpaceBook.LambdaIndexPCA
