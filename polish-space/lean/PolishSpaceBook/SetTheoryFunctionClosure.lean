module

public import PolishSpaceBook.SetTheoryFunctionFormulas
public import PolishSpaceBook.SetTheoryProducts

@[expose] public section

/-! # Internal function spaces and graphs of internally definable maps -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

abbrev functionSeparationFormula : ForcingFormulas.Formula 3 := functionFormula 0 1 2

/-- The internal function space contains exactly the actual functions that belong to the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The product lemma gives $x\times y\in M$, so the internal Power Set axiom gives
    $$B=\PowerSet{x\times y}\cap M\in M.$$
    Every actual function from $x$ to $y$ is a subset of $x\times y$.
    The bounded function predicate recognizes the actual function graphs in any transitive domain, as proved in
    §{sec:zfc-absoluteness}. Separation therefore gives
    $$\{g\in B:g:x\to y\}=\funcspace{x}{y}\cap M\in M.$$
    This does not imply that every external function between those sets belongs to $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Function spaces and definable graphs in a transitive model
-/
theorem internal_funs_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hprod : M ⊨ separationSentence productSeparationFormula)
    (hfunc : M ⊨ separationSentence functionSeparationFormula)
    {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) : (ZFSet.funs x y ∩ M) ∈ M := by
  let B := internalPowerSet M (ZFSet.prod x y)
  have hB : B ∈ M := internalPowerSet_mem hM hpower
    (prod_mem_of_separation hM hpair hunion hpower hprod hx hy)
  let ps : Fin 2 → M := ![⟨x, hx⟩, ⟨y, hy⟩]
  have hps : (fun i => (ps i).val) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  have h := delta_zero_separation_mem hM functionSeparationFormula
    (functionFormula_deltaZero _ _ _) hfunc ps hB
  have heq : B.sep (fun f => externalRealize functionSeparationFormula
      (Fin.snoc (fun i => (ps i).val) f)) = ZFSet.funs x y ∩ M := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, hps, external_functionFormula, ZFSet.mem_inter, ZFSet.mem_funs]
    change (f ∈ M.sep (fun z => z ⊆ ZFSet.prod x y)) ∧ ZFSet.IsFunc x y f ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, h.1.1⟩, h.1⟩⟩
  exact heq ▸ h

/-- A graph collected from a function on a set, without an ambient definability assumption. -/
def functionGraph {x : ZFSet.{u}} (f : x → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun a : x => ZFSet.pair a.val (f a))

lemma functionGraph_isFunc {x : ZFSet.{u}} (f : x → ZFSet.{u}) :
    ZFSet.IsFunc x (ZFSet.range f) (functionGraph f) := by
  constructor
  · intro z hz
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨a.property, ZFSet.mem_range.mpr ⟨a, rfl⟩⟩
  · intro a ha
    refine ⟨f ⟨a, ha⟩, ZFSet.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨c, hc⟩ := ZFSet.mem_range.mp hb
    obtain ⟨hca, hfb⟩ := ZFSet.pair_inj.mp hc
    have he : c = ⟨a, ha⟩ := Subtype.ext hca
    simpa only [he] using hfb.symm

/-- Turn a value-defining formula into a formula defining the corresponding ordered pair. -/
def graphSelector {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  ((reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc) (Fin.last (n + 2)))) ⊓
    orderedPairFormula (Fin.last (n + 1)).castSucc (Fin.last n).castSucc.castSucc (Fin.last (n + 2))).ex

lemma realize_graphSelector (S : ZFSet.{u}) (hS : S.IsTransitive)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → S) (a q : S) :
    (graphSelector φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) q) ↔
      ∃ b : S, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ∧ q.val = ZFSet.pair a.val b.val := by
  have hp {k : ℕ} (q a b : Fin k) (xs : Fin k → S) :
      (orderedPairFormula q a b).Realize Empty.elim xs ↔
        (xs q).val = ZFSet.pair (xs a).val (xs b).val :=
    realize_orderedPairFormula (S : ZFClass) (fun _ ha _ hb => hS.mem_trans hb ha) q a b xs
  simp only [graphSelector, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, hp,
    apply_snoc, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]

/-- Replacement for the ordered-pair selector collects the actual graph in the ground model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For the second assertion, take $a\in x$. Transitivity gives $a\in M$, and the assumed internal definition
    supplies the unique value $f(a)\in M$. Pairing puts $\langle a,f(a)\rangle$ in $M$.
    The bounded ordered-pair formula identifies this actual pair, so $\theta(a,q,\vec p)$ holds internally exactly
    when $q=\langle a,f(a)\rangle$. Apply the definable-image lemma to this pair-valued function to obtain
    $\Gamma_f\in M$.
    Every member of $\Gamma_f$ is one of these pairs, and each $a\in x$ occurs once, so
    $\Gamma_f:x\to f[x]$. Uniqueness follows from injectivity of ordered-pair coding.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Function spaces and definable graphs in a transitive model
-/
theorem replacement_graph_mem {S : ZFSet.{u}} (hS : S.IsTransitive)
    (hpair : S ⊨ pairingSentence) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (hrep : S ⊨ replacementSentence (graphSelector φ))
    (ps : Fin n → S) {x : ZFSet.{u}} (hx : x ∈ S) (f : x → S)
    (hf : ∀ a : x, ∀ b : S,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps ⟨a.val, hS.mem_trans a.property hx⟩) b) ↔ b = f a) :
    functionGraph (fun a => (f a).val) ∈ S := by
  let g : x → S := fun a =>
    ⟨ZFSet.pair a.val (f a).val, orderedPair_mem hS hpair (hS.mem_trans a.property hx) (f a).property⟩
  apply replacement_image_mem hS (graphSelector φ) hrep ps hx g
  intro a q
  rw [realize_graphSelector S hS]
  constructor
  · rintro ⟨b, hb, hq⟩
    have he := (hf a b).mp hb
    apply Subtype.ext
    simpa only [he] using hq
  · intro hq
    refine ⟨f a, (hf a (f a)).mpr rfl, ?_⟩
    exact congrArg Subtype.val hq

end PolishSpaceBook.SetTheoryModels
