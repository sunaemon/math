module

public import PolishSpaceBook.SetTheoryFunctionClosure

@[expose] public section

/-! # Restricting set-coded graphs, with bounded Separation inside a model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Both coordinates of any pair in f lie in its double union. -/
lemma second_mem_doubleUnion {a b f : ZFSet.{u}} (h : ZFSet.pair a b ∈ f) :
    b ∈ ZFSet.sUnion (ZFSet.sUnion f) := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨{a, b}, ZFSet.mem_sUnion.mpr ⟨ZFSet.pair a b, h, ?_⟩, ?_⟩ <;> simp [ZFSet.pair]

/-- Restriction to inputs in x, with the output quantifier bounded by the graph itself. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Restrictions of graphs can also be formed internally. Put $B=\bigcup\bigcup f$.
    If $\langle a,b\rangle\in f$, then $b\in\{a,b\}\in\langle a,b\rangle\in f$, so $b\in B$.
    Consequently
    $$\restrict{f}{x}=\{q\in f:\exists a\in x\,\exists b\in B\,(q=\langle a,b\rangle)\}.$$
    For a function graph, this keeps exactly the pairs whose first coordinate lies in $x$.
    If $f,x\in M$, two applications of Union put $B$ in $M$, and bounded Separation gives $\restrict{f}{x}\in M$.
    No bound on the values external to the graph is needed.
-/
def restrictGraph (f x : ZFSet.{u}) : ZFSet.{u} :=
  f.sep (fun p => p ∈ ZFSet.prod x (ZFSet.sUnion (ZFSet.sUnion f)))

lemma pair_mem_restrictGraph {f x a b : ZFSet.{u}} :
    ZFSet.pair a b ∈ restrictGraph f x ↔ ZFSet.pair a b ∈ f ∧ a ∈ x := by
  rw [restrictGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, second_mem_doubleUnion h.1⟩⟩

lemma mem_restrictGraph {f x p : ZFSet.{u}} :
    p ∈ restrictGraph f x ↔ ∃ a ∈ x, ∃ b, p = ZFSet.pair a b ∧ ZFSet.pair a b ∈ f := by
  constructor
  · intro hp
    obtain ⟨hf, a, ha, b, _, he⟩ := (ZFSet.mem_sep.mp hp).imp_right ZFSet.mem_prod.mp
    exact ⟨a, ha, b, he, he ▸ hf⟩
  · rintro ⟨a, ha, b, rfl, hf⟩
    exact pair_mem_restrictGraph.mpr ⟨hf, ha⟩

lemma isFunc_restrictGraph {D Y f x : ZFSet.{u}} (hf : ZFSet.IsFunc D Y f) (hx : x ⊆ D) :
    ZFSet.IsFunc x Y (restrictGraph f x) := by
  constructor
  · intro p hp
    obtain ⟨a, ha, b, rfl, hab⟩ := mem_restrictGraph.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨ha, (ZFSet.pair_mem_prod.mp (hf.1 hab)).2⟩
  · intro a ha
    obtain ⟨b, hb, huniq⟩ := hf.2 a (hx ha)
    exact ⟨b, pair_mem_restrictGraph.mpr ⟨hb, ha⟩,
      fun c hc => huniq c (pair_mem_restrictGraph.mp hc).1⟩

lemma isFunc_doubleUnion {D Y f : ZFSet.{u}} (hf : ZFSet.IsFunc D Y f) :
    ZFSet.IsFunc D (ZFSet.sUnion (ZFSet.sUnion f)) f := by
  refine ⟨?_, hf.2⟩
  intro p hp
  obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
  exact ZFSet.pair_mem_prod.mpr ⟨ha, second_mem_doubleUnion hp⟩

/-- Pointwise agreement on a common subdomain identifies the two restricted graphs. -/
lemma restrictGraph_eq_of_agree {D E Y Z f g x : ZFSet.{u}}
    (hf : ZFSet.IsFunc D Y f) (hg : ZFSet.IsFunc E Z g) (hxD : x ⊆ D) (hxE : x ⊆ E)
    (h : ∀ a ∈ x, ∀ b c, ZFSet.pair a b ∈ f → ZFSet.pair a c ∈ g → b = c) :
    restrictGraph f x = restrictGraph g x := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨a, ha, b, rfl, hab⟩ := mem_restrictGraph.mp hp
    obtain ⟨c, hac, _⟩ := hg.2 a (hxE ha)
    have he := h a ha b c hab hac
    exact pair_mem_restrictGraph.mpr ⟨he ▸ hac, ha⟩
  · intro hp
    obtain ⟨a, ha, c, rfl, hac⟩ := mem_restrictGraph.mp hp
    obtain ⟨b, hab, _⟩ := hf.2 a (hxD ha)
    have he := h a ha b c hab hac
    exact pair_mem_restrictGraph.mpr ⟨he ▸ hab, ha⟩

/-- Two unions and bounded Separation suffice to restrict an internal graph. -/
theorem restrictGraph_mem {M f x : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hsep : M ⊨ separationSentence productSeparationFormula)
    (hf : f ∈ M) (hx : x ∈ M) : restrictGraph f x ∈ M := by
  let B := ZFSet.sUnion (ZFSet.sUnion f)
  have hB : B ∈ M := union_mem hM hunion (union_mem hM hunion hf)
  let ps : Fin 2 → M := ![⟨x, hx⟩, ⟨B, hB⟩]
  have hps : (fun i => (ps i).val) = ![x, B] := by
    funext i
    fin_cases i <;> rfl
  have h := delta_zero_separation_mem hM productSeparationFormula
    (productFormula_deltaZero _ _ _) hsep ps hf
  have heq : f.sep (fun p => externalRealize productSeparationFormula
      (Fin.snoc (fun i => (ps i).val) p)) = restrictGraph f x := by
    apply ZFSet.ext
    intro p
    rw [restrictGraph, ZFSet.mem_sep, ZFSet.mem_sep, hps, external_productFormula]
  exact heq ▸ h

/-- Adding a pair outside the restricted domain leaves the restriction unchanged. -/
lemma restrictGraph_insert_of_notMem {f x a b : ZFSet.{u}} (ha : a ∉ x) :
    restrictGraph (insert (ZFSet.pair a b) f) x = restrictGraph f x := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨z, hz, w, rfl, hzw⟩ := mem_restrictGraph.mp hp
    rcases ZFSet.mem_insert_iff.mp hzw with he | hf
    · have hza := (ZFSet.pair_inj.mp he).1
      exact False.elim (ha (hza ▸ hz))
    · exact pair_mem_restrictGraph.mpr ⟨hf, hz⟩
  · intro hp
    obtain ⟨z, hz, w, rfl, hzw⟩ := mem_restrictGraph.mp hp
    exact pair_mem_restrictGraph.mpr ⟨ZFSet.mem_insert_iff.mpr (Or.inr hzw), hz⟩

end PolishSpaceBook.SetTheoryModels
