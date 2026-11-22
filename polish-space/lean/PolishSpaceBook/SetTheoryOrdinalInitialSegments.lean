module

public import PolishSpaceBook.SetTheoryOrdinalIsoFormulas

@[expose] public section

/-! # Internal predecessor segments of ordinal representations

Restrictions are formed by Separation, rather than by assuming external subset
closure of the model. The restricted graph is the unique ordinal representation
of its predecessor segment.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def orderPredecessors (A R a : ZFSet.{u}) : ZFSet.{u} :=
  A.sep (fun x => pair x a ∈ R)

lemma mem_orderPredecessors {A R a x : ZFSet.{u}} :
    x ∈ orderPredecessors A R a ↔ x ∈ A ∧ pair x a ∈ R := ZFSet.mem_sep

lemma orderPredecessors_mem {M A R a : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : M ⊨ separationSentence (pairMemberFormula (0 : Fin 3) 2 1))
    (hA : A ∈ M) (hR : R ∈ M) (ha : a ∈ M) : orderPredecessors A R a ∈ M := by
  apply separation_mem_of_absolute hM (pairMemberFormula (0 : Fin 3) 2 1) hsep
    ![⟨R, hR⟩, ⟨a, ha⟩] hA (fun x => pair x a ∈ R)
  intro x _
  simpa [Fin.snoc] using realize_pairMemberFormula_model hM (0 : Fin 3) 2 1
    (Fin.snoc ![⟨R, hR⟩, ⟨a, ha⟩] x)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The bounded pair-membership formula defines $D_a$ by Separation on $W$.
    The recognition lemma makes $f$ an actual order-isomorphism onto the actual ordinal $\alpha$.
    Thus $\beta_a\in\alpha\in M$, and transitivity gives $\beta_a\in M$.
    Graph restriction in §{sec:internal-model-closure} puts $g_a$ in $M$ using Union and Separation.

    For $x\in D_a$, preservation of the order gives $f(x)\in f(a)=\beta_a$.
    Conversely, if $b\in\beta_a$, transitivity of $\alpha$ gives $b\in\alpha$.
    Surjectivity supplies $x\in W$ with $f(x)=b$, and reflection of the order gives
    $\langle x,a\rangle\in R$. Hence $x\in D_a$.
    The restriction is therefore onto $\beta_a$, remains injective, and preserves and reflects the relation.
    Since a member of an ordinal is an ordinal, the recognition lemma gives the displayed internal assertion.
    Its uniqueness clause proves the last assertion.
    \end{proof}
-/
def ordinalIsoInitial {A R α : ZFSet.{u}} (hα : α.IsOrdinal)
    (e : (fun x y : A => pair x.val y.val ∈ R) ≃r (fun b c : α => b.val ∈ c.val)) (a : A) :
    (fun x y : orderPredecessors A R a.val => pair x.val y.val ∈ R) ≃r
      (fun b c : (e a).val => b.val ∈ c.val) := by
  let g : orderPredecessors A R a.val → (e a).val := fun x =>
    ⟨(e ⟨x.val, (mem_orderPredecessors.mp x.property).1⟩).val,
      e.map_rel_iff.mpr (mem_orderPredecessors.mp x.property).2⟩
  have hi : Function.Injective g := by
    intro x y he
    have he' : (e ⟨x.val, (mem_orderPredecessors.mp x.property).1⟩).val =
        (e ⟨y.val, (mem_orderPredecessors.mp y.property).1⟩).val :=
      congrArg (fun z : (e a).val => z.val) he
    exact Subtype.ext (congrArg (fun z : A => z.val) (e.injective (Subtype.ext he')))
  have hs : Function.Surjective g := by
    intro b
    let bα : α := ⟨b.val, hα.isTransitive.mem_trans b.property (e a).property⟩
    let x := e.symm bα
    have hx : pair x.val a.val ∈ R := by
      apply e.map_rel_iff.mp
      simpa only [x, RelIso.apply_symm_apply] using b.property
    refine ⟨⟨x.val, mem_orderPredecessors.mpr ⟨x.property, hx⟩⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : α => z.val) (e.apply_symm_apply bα)
  exact { Equiv.ofBijective g ⟨hi, hs⟩ with map_rel_iff' := e.map_rel_iff }

lemma ordinalIsoInitial_graph {A R α : ZFSet.{u}} (hα : α.IsOrdinal)
    (e : (fun x y : A => pair x.val y.val ∈ R) ≃r (fun b c : α => b.val ∈ c.val)) (a : A) :
    functionGraph (fun x => (ordinalIsoInitial hα e a x).val) =
      restrictGraph (functionGraph (fun x => (e x).val)) (orderPredecessors A R a.val) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hp
    apply pair_mem_restrictGraph.mpr
    exact ⟨ZFSet.mem_range.mpr ⟨⟨x.val, (mem_orderPredecessors.mp x.property).1⟩, rfl⟩, x.property⟩
  · intro hp
    obtain ⟨x, hx, b, hpEq, hpf⟩ :=
      (mem_restrictGraph (f := functionGraph (fun x => (e x).val))
        (x := orderPredecessors A R a.val)).mp hp
    subst p
    obtain ⟨y, he⟩ := ZFSet.mem_range.mp hpf
    obtain ⟨hy, _⟩ := ZFSet.pair_injective he
    exact ZFSet.mem_range.mpr ⟨⟨x, hx⟩, by
      change pair x (e ⟨x, (mem_orderPredecessors.mp hx).1⟩).val = pair x b
      have hey : y = ⟨x, (mem_orderPredecessors.mp hx).1⟩ := Subtype.ext hy
      simpa only [hey] using he⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal restriction of ordinal representations
-/
theorem internal_ordinalIso_initial {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (A R α f : M) (hf : ordinalIsoFormula.Realize Empty.elim ![A, R, α, f])
    (a : A.val) :
    ∃ D β g : M, D.val = orderPredecessors A.val R.val a.val ∧
      pair a.val β.val ∈ f.val ∧ g.val = restrictGraph f.val D.val ∧
      ordinalIsoFormula.Realize Empty.elim ![D, R, β, g] := by
  obtain ⟨hα, e, he⟩ := (realize_ordinalIsoFormula hM A R α f).mp hf
  let D : M := ⟨orderPredecessors A.val R.val a.val,
    orderPredecessors_mem hM (hsep _) A.property R.property (hM.mem_trans a.property A.property)⟩
  let β : M := ⟨(e a).val, hM.mem_trans (e a).property α.property⟩
  let g : M := ⟨restrictGraph f.val D.val, restrictGraph_mem hM hunion (hsep _) f.property D.property⟩
  refine ⟨D, β, g, rfl, ?_, rfl, ?_⟩
  · rw [← he]
    exact ZFSet.mem_range.mpr ⟨a, rfl⟩
  · apply (realize_ordinalIsoFormula hM D R β g).mpr
    refine ⟨hα.mem (e a).property, ordinalIsoInitial hα e a, ?_⟩
    simpa only [he] using ordinalIsoInitial_graph hα e a

end PolishSpaceBook.SetTheoryModels
