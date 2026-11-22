module

public import PolishSpaceBook.SetTheoryInternalIteration
public import PolishSpaceBook.SetTheoryChoice
public import PolishSpaceBook.SetTheoryInitialOrdinalFormulas

@[expose] public section

/-! # Internal dependent choice for a serial set-coded relation

Choose a predecessor from each nonempty predecessor set, then construct the
whole infinite iteration graph internally. The orientation is descending:
the next value is related to the current value.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters B,R,c,p; p pairs x with the choice from its predecessor set. -/
def predecessorSelectorFormula : ForcingFormulas.Formula 4 :=
  boundedExists 0 (boundedExists 0
    ((predecessorFormula (0 : Fin 7) 1 4 6 ⊓ pairMemberFormula 2 6 5 ⊓
      orderedPairFormula 3 4 5).ex))

def predecessorSelectorGraph (B R c : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod B B).sep (fun p =>
    ∃ x ∈ B, ∃ y ∈ B, p = pair x y ∧ pair (orderPredecessors B R x) y ∈ c)

lemma pair_mem_predecessorSelectorGraph {B R c x y : ZFSet.{u}} :
    pair x y ∈ predecessorSelectorGraph B R c ↔
      x ∈ B ∧ y ∈ B ∧ pair (orderPredecessors B R x) y ∈ c := by
  rw [predecessorSelectorGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, _, b, _, he, hp⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx, hy, hp⟩
  · rintro ⟨hx, hy, hp⟩
    exact ⟨⟨hx, hy⟩, x, hx, y, hy, rfl, hp⟩

lemma realize_predecessorSelectorFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (B R c p : M) :
    predecessorSelectorFormula.Realize Empty.elim ![B, R, c, p] ↔
      ∃ x ∈ B.val, ∃ y ∈ B.val, p.val = pair x y ∧
        pair (orderPredecessors B.val R.val x) y ∈ c.val := by
  have hp {n : ℕ} (q a b : Fin n) (xs : Fin n → M) :
      (orderedPairFormula q a b).Realize Empty.elim xs ↔
        (xs q).val = pair (xs a).val (xs b).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q a b xs
  simp only [predecessorSelectorFormula, realize_boundedExists_model, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, realize_predecessorFormula hM, realize_pairMemberFormula_model hM,
    hp, Fin.snoc]
  constructor
  · rintro ⟨x, hx, y, hy, D, ⟨hD, hc⟩, hp⟩
    exact ⟨x.val, hx, y.val, hy, hp, hD ▸ hc⟩
  · rintro ⟨x, hx, y, hy, hp, hc⟩
    have hxM := hM.mem_trans hx B.property
    exact ⟨⟨x, hxM⟩, hx, ⟨y, hM.mem_trans hy B.property⟩, hy,
      ⟨orderPredecessors B.val R.val x,
        orderPredecessors_mem hM (hsep _) B.property R.property hxM⟩, ⟨rfl, hc⟩, hp⟩

lemma predecessorSelectorGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (B R c : M) : predecessorSelectorGraph B.val R.val c.val ∈ M := by
  apply separation_mem_of_absolute hM predecessorSelectorFormula (hsep _) ![B, R, c]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) B.property B.property)
  intro p _
  have he : Fin.snoc ![B, R, c] p = ![B, R, c, p] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact realize_predecessorSelectorFormula hM hsep B R c p

/-- Seriality supplies an internal next-state function, with descending orientation. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Take an internal choice function $c_0$ on the nonempty internal subsets of $B$. For $x\in B$, Separation gives
    $$D_x:=\{y\in B:\langle y,x\rangle\in R\}\in M.$$
    The hypothesis makes $D_x$ nonempty. Define $d(x)=c_0(D_x)$. Its graph belongs to $M$: separate from $B\times B$
    the pairs $\langle x,y\rangle$ for which there is a set $V$ satisfying
    $$V=D_x\quad\text{and}\quad\langle V,y\rangle\in c_0.$$
    Expand $V=D_x$ by its membership clause. The set $D_x\in M$ supplies the witness internally, and the unique value
    of $c_0$ makes this a function graph $d:B\to B$. Each value satisfies $\langle d(x),x\rangle\in R$.
-/
theorem internal_predecessor_selector {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hchoice : M ⊨ choiceSentence) (B R : M)
    (hserial : ∀ x ∈ B.val, ∃ y ∈ B.val, pair y x ∈ R.val) :
    ∃ d : M, IsFunc B.val B.val d.val ∧
      ∀ x y, pair x y ∈ d.val → pair y x ∈ R.val := by
  obtain ⟨c, hc, hs⟩ := internal_subset_choice hM hunion hpower (hsep _) hchoice B.property
  have hD (x : ZFSet.{u}) (hx : x ∈ B.val) :
      orderPredecessors B.val R.val x ∈ internalNonemptySubsets M B.val := by
    obtain ⟨y, hy, hyx⟩ := hserial x hx
    exact mem_internalNonemptySubsets.mpr
      ⟨⟨orderPredecessors_mem hM (hsep _) B.property R.property (hM.mem_trans hx B.property),
        fun _ hz => (mem_orderPredecessors.mp hz).1⟩,
        y, mem_orderPredecessors.mpr ⟨hy, hyx⟩⟩
  let d : M := ⟨predecessorSelectorGraph B.val R.val c.val,
    predecessorSelectorGraph_mem hM hpair hunion hpower hsep B R c⟩
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    change p ∈ predecessorSelectorGraph B.val R.val c.val at hp
    exact (ZFSet.mem_sep.mp hp).1
  · intro x hx
    obtain ⟨y, hy, hcy⟩ := hs _ (hD x hx)
    refine ⟨y, pair_mem_predecessorSelectorGraph.mpr
      ⟨hx, (mem_orderPredecessors.mp hy).1, hcy⟩, ?_⟩
    intro z hz
    exact (hc.2 _ (hD x hx)).unique (pair_mem_predecessorSelectorGraph.mp hz).2.2 hcy
  · intro x y hxy
    obtain ⟨hx, _, hcy⟩ := pair_mem_predecessorSelectorGraph.mp hxy
    obtain ⟨z, hz, hcz⟩ := hs _ (hD x hx)
    have he : y = z := (hc.2 _ (hD x hx)).unique hcy hcz
    exact he ▸ (mem_orderPredecessors.mp hz).2

/-- A descending sequence starting at any specified element has its graph in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal dependent choice
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Apply the iteration lemma to $d$ and the specified starting point $a$.
-/
theorem internal_dependent_choice {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hchoice : M ⊨ choiceSentence) (B R : M)
    (hserial : ∀ x ∈ B.val, ∃ y ∈ B.val, pair y x ∈ R.val) (a : B.val) :
    ∃ s : ℕ → ZFSet.{u}, s 0 = a.val ∧ (∀ n, s n ∈ B.val) ∧
      (∀ n, pair (s (n + 1)) (s n) ∈ R.val) ∧ sequenceGraph s ∈ M := by
  obtain ⟨d, hd, hr⟩ := internal_predecessor_selector hM hpair hunion hpower hsep hchoice B R hserial
  obtain ⟨s, h0, hs, hstep, hgraph⟩ := internal_function_iteration hM hinf hpair hunion hpower hsep B d hd a
  exact ⟨s, h0, hs, fun n => hr _ _ (hstep n), hgraph⟩

end PolishSpaceBook.SetTheoryModels
