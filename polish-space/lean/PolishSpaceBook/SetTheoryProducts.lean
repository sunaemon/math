module

public import PolishSpaceBook.SetTheoryPairFormulas

@[expose] public section

/-! # Cartesian products in a transitive model, using internal power sets -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

abbrev productSeparationFormula : ForcingFormulas.Formula 3 := productFormula 0 1 2

/-- Two internal power sets bound all ordered pairs, because their constituents are in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Use the elementary closure lemma to form the following sets in $M$:
    $$A=x\cup y,\qquad B=\PowerSet{A}\cap M,\qquad C=\PowerSet{B}\cap M.$$
    If $a\in x$ and $b\in y$, transitivity gives $a,b\in M$. Pairing puts
    $\{a\}$, $\{a,b\}$, and $\langle a,b\rangle$ in $M$.
    The first two sets are subsets of $A$, so they belong to $B$.
    Hence $\langle a,b\rangle$ is a subset of $B$ and belongs to $M$, which puts it in $C$.
    Thus $x\times y\IncludedIn C$.
-/
lemma pair_mem_internal_double_power {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) {x y a b : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M)
    (ha : a ∈ x) (hb : b ∈ y) :
    ZFSet.pair a b ∈ internalPowerSet M (internalPowerSet M (x ∪ y)) := by
  have haM := hM.mem_trans ha hx
  have hbM := hM.mem_trans hb hy
  have hs : ({a} : ZFSet.{u}) ∈ internalPowerSet M (x ∪ y) := by
    rw [internalPowerSet, ZFSet.mem_sep]
    refine ⟨singleton_mem hM hpair haM, ?_⟩
    intro z hz
    rw [ZFSet.mem_singleton] at hz
    subst z
    exact ZFSet.mem_union.mpr (Or.inl ha)
  have hp : ({a, b} : ZFSet.{u}) ∈ internalPowerSet M (x ∪ y) := by
    rw [internalPowerSet, ZFSet.mem_sep]
    refine ⟨unorderedPair_mem hM hpair haM hbM, ?_⟩
    intro z hz
    rcases ZFSet.mem_pair.mp hz with rfl | rfl
    · exact ZFSet.mem_union.mpr (Or.inl ha)
    · exact ZFSet.mem_union.mpr (Or.inr hb)
  rw [internalPowerSet, ZFSet.mem_sep]
  refine ⟨orderedPair_mem hM hpair haM hbM, ?_⟩
  intro z hz
  rcases ZFSet.mem_pair.mp hz with rfl | rfl
  · exact hs
  · exact hp

/-- Cartesian-product closure using only internal power sets and bounded Separation. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The predicate $\exists a\in x\,\exists b\in y\,(q=\langle a,b\rangle)$ is $\Delta_0$ after the bounded
    ordered-pair expansion in §{sec:zfc-absoluteness}. Bounded Separation therefore gives
    $$x\times y=\{q\in C:\exists a\in x\,\exists b\in y\,(q=\langle a,b\rangle)\}\in M.$$
    Both power sets used in the argument are internal power sets. No external power-set closure is assumed.
    The required Separation instance can itself be obtained from Infinity and one Replacement instance by
    §{sec:zfc-axioms}.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Cartesian products in a transitive model
-/
theorem prod_mem_of_separation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence productSeparationFormula)
    {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) : ZFSet.prod x y ∈ M := by
  let B := internalPowerSet M (internalPowerSet M (x ∪ y))
  have hB : B ∈ M := internalPowerSet_mem hM hpower
    (internalPowerSet_mem hM hpower (binaryUnion_mem hM hpair hunion hx hy))
  have hsub : ZFSet.prod x y ⊆ B := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hz
    exact pair_mem_internal_double_power hM hpair hx hy ha hb
  let ps : Fin 2 → M := ![⟨x, hx⟩, ⟨y, hy⟩]
  have hps : (fun i => (ps i).val) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  have h := delta_zero_separation_mem hM
    productSeparationFormula (productFormula_deltaZero _ _ _) hsep ps hB
  have heq : B.sep (fun z => externalRealize productSeparationFormula
      (Fin.snoc (fun i => (ps i).val) z)) = ZFSet.prod x y := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, hps, external_productFormula]
    exact ⟨And.right, fun hz => ⟨hsub hz, hz⟩⟩
  exact heq ▸ h

/-- The required Separation instance follows from a single Replacement instance. -/
theorem prod_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hrep : M ⊨ replacementSentence (singletonSelector productSeparationFormula))
    {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) : ZFSet.prod x y ∈ M :=
  prod_mem_of_separation hM hpair hunion hpower
    (models_separation_of_replacement M (models_extensionality hM) hinf hpair hunion
      productSeparationFormula hrep) hx hy

end PolishSpaceBook.SetTheoryModels
