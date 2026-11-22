module

public import PolishSpaceBook.ForcingChoice
public import PolishSpaceBook.ForcingOrdinalPreservation
public import PolishSpaceBook.ForcingDecisionClosure
public import PolishSpaceBook.SetTheoryDefinitionalExtensions

@[expose] public section

/-! # The generic extension satisfies the literal full ZFC theory

Assemble the separate name constructions for each axiom. Genericity is given;
external countability of the ground model is not needed here.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $M \models \mathrm{ZFC}$ and $G$ is $M$-generic for $P \in M$, then $M[G]$ is again a transitive model of ZFC,
    contains $M$, and has $G$ as an element. More precisely:
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The preceding arguments establish Extensionality, Foundation, Pairing, Union, and Infinity using transitivity,
    concrete name valuations, and the internal closure constructions.
-/
theorem extension_models_fullZFC {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hZFC : M ⊨ fullZFCTheory) (P R : M) [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    Extension P.val M G ⊨ fullZFCTheory := by
  have hi := hZFC.realize_of_mem _ ZFCAxiom.infinity
  have hp := hZFC.realize_of_mem _ ZFCAxiom.pairing
  have hu := hZFC.realize_of_mem _ ZFCAxiom.union
  have hpow := hZFC.realize_of_mem _ ZFCAxiom.power
  have hc := hZFC.realize_of_mem _ ZFCAxiom.choice
  have hs {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)) : M ⊨ separationSentence φ :=
    fullZFC_model_separation hZFC φ
  have hr {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)) : M ⊨ replacementSentence φ :=
    hZFC.realize_of_mem _ (ZFCAxiom.replacement φ)
  have hg : ∃ p ∈ chosen P.val G, p ∈ P.val := by
    obtain ⟨p, hpG⟩ := G.nonempty
    exact ⟨p.val, ⟨p, hpG, rfl⟩, p.property⟩
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  constructor
  intro φ hφ
  cases hφ with
  | extensionality => exact models_extensionality hE
  | foundation => exact models_foundation hE
  | pairing => exact extension_models_pairing hM hi hp hu hpow (hr _) P.property (chosen P.val G) hg
  | union => exact extension_models_union hM hi hp hu hpow (hr _) (hr _) P.property R.property hR G
  | power => exact extension_models_power hM hi hp hu hpow hs hr P R hR G hG
  | infinity => exact extension_models_infinity hM hi hp hu hpow hs hr P.property (chosen P.val G) hg
  | choice => exact extension_models_choice hM hi hp hu hpow hs hr hc P R hR G hG
  | replacement φ => exact extension_models_replacement hM hi hp hu hpow hs hr P R hR G hG φ

/-- The other basic extension facts use the same axiom-derived closures. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $M \IncludedIn M[G]$ via $x=\check{x}^G$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $G=\dot G^G \in M[G]$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $M$ and $M[G]$ have the same ordinals.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    it does not add new ordinals.
-/
theorem fullZFC_extension_properties {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hZFC : M ⊨ fullZFCTheory) (P : M) [Preorder (Condition P.val)]
    (G : Order.PFilter (Condition P.val)) :
    (extension P.val M (chosen P.val G)).IsTransitive ∧
      M ⊆ extension P.val M (chosen P.val G) ∧
      P.val.sep (fun p => p ∈ chosen P.val G) ∈ extension P.val M (chosen P.val G) ∧
      ∀ α : ZFSet.{u}, α.IsOrdinal →
        (α ∈ extension P.val M (chosen P.val G) ↔ α ∈ M) := by
  have hi := hZFC.realize_of_mem _ ZFCAxiom.infinity
  have hp := hZFC.realize_of_mem _ ZFCAxiom.pairing
  have hu := hZFC.realize_of_mem _ ZFCAxiom.union
  have hpow := hZFC.realize_of_mem _ ZFCAxiom.power
  have hs {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)) : M ⊨ separationSentence φ :=
    fullZFC_model_separation hZFC φ
  have hr {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)) : M ⊨ replacementSentence φ :=
    hZFC.realize_of_mem _ (ZFCAxiom.replacement φ)
  have hg : ∃ p ∈ chosen P.val G, p ∈ P.val := by
    obtain ⟨p, hpG⟩ := G.nonempty
    exact ⟨p.val, ⟨p, hpG, rfl⟩, p.property⟩
  exact ⟨extension_isTransitive P.val M (chosen P.val G) hM,
    ground_subset_extension_of_axioms hM hi hp hu hpow hs hr P.property (chosen P.val G) hg,
    genericFilter_mem_extension hM hi hp hu hpow hs hr P (chosen P.val G) hg,
    fun _ hα => ordinal_mem_extension_iff_of_axioms hM hi hp hu hpow hs hr
      P.property (chosen P.val G) hg hα⟩

/-- Valuation closure gives the stated minimality; transitivity and ZFC in the
comparison model are stronger than this implication needs. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $M[G]$ is generated from $M\cup\{G\}$ by valuing the $P$-names in $M$; equivalently, any transitive ZFC model
        containing $M\cup\{G\}$ and closed under this name valuation contains $M[G]$.
-/
theorem extension_subset_iff_valuation_closed (P M N : ZFSet.{u}) (G : Set ZFSet.{u}) :
    extension P M G ⊆ N ↔ ∀ τ ∈ M, IsName P τ → valuation G τ ∈ N := by
  constructor
  · intro h τ hτ hn
    exact h ((mem_extension P M G _).mpr ⟨τ, hτ, hn, rfl⟩)
  · intro h x hx
    obtain ⟨τ, hτ, hn, rfl⟩ := (mem_extension P M G x).mp hx
    exact h τ hτ hn

end PolishSpaceBook.SetTheoryModels
