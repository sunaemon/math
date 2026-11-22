module

public import PolishSpaceBook.FirstOrderGraphUniqueness

@[expose] public section

/-!
# Two values of one operation graph are equal

Fresh auxiliary output names keep the comparison proof independent of the
actual input and output names, even when those actual names overlap.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Substitution for an output absent from the inputs changes only that output. -/
theorem operationGraph_subst_output {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts : Fin n → L.Term ℕ) (x y : ℕ) (hx : ∀ i, x ∉ (ts i).varFinset) :
    (D.operationGraph f ts x).subst x (.var y) = D.operationGraph f ts y := by
  rw [D.operationGraph_eq_instance, D.operationGraph_eq_instance,
    simultaneous_subst _ _ _ _ (D.fv_operationTemplate f)]
  congr 1
  funext i
  cases i using Fin.lastCases with
  | last => simp only [Fin.snoc_last, Term.subst, ite_true]
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact termSubst_not_free (ts i) x (.var y) (hx i)

/-- The old theory proves equality of any two outputs at the same named inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Consequently, two values satisfying the same operation graph are provably equal. To keep their actual names
    unrestricted, choose auxiliary output and comparison names fresh for the inputs and both values. From unique
    existence and the graph at the first value, the graph-replacement proof gives a universal characterization of
    all graph values. Instantiate it at the second value and use its graph assumption. This gives equality of the
    second value with the first; symmetry gives the desired orientation. The auxiliary names are not free in the
    added graph assumptions, so all eigenvariable conditions remain valid.
-/
theorem proves_operationGraph_functional {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ}
    (f : (L.sum (functionSymbols ι)).Functions n) (a : Fin n → ℕ) (ha : Function.Injective a)
    (x y : ℕ) : ProvesFrom T (binary .imp
      (binary .conj (D.operationGraph f (fun i => .var (a i)) x)
        (D.operationGraph f (fun i => .var (a i)) y)) (equal (.var x) (.var y))) := by
  let ts : Fin n → L.Term ℕ := fun i => .var (a i)
  let S := argumentVars ts ∪ {x,y}
  let p := NamedLambda.Term.fresh S
  let q := NamedLambda.Term.fresh (insert p S)
  have hp : p ∉ S := NamedLambda.Term.fresh_not_mem S
  have hq : q ≠ p ∧ q ∉ S := by
    simpa only [Finset.mem_insert, not_or] using NamedLambda.Term.fresh_not_mem (insert p S)
  have fresh (w : ℕ) (hw : w ∉ S) :
      w ∉ argumentVars ts ∧ w ≠ x ∧ w ≠ y := by
    simpa only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] using hw
  have hp' := fresh p hp
  have hq' := fresh q hq.2
  have outside (w : ℕ) (hw : w ∉ argumentVars ts) : w ∉ Set.range a := by
    rintro ⟨i,rfl⟩
    exact hw (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,by simp [ts]⟩)
  obtain ⟨Γ,hΓ,huniq⟩ := D.proves_operationGraph_unique hT hu f a ha p q (Ne.symm hq.1)
    (outside p hp'.1) (outside q hq'.1)
  have hc := Context.fv_eq_empty_of_sentences hT Γ hΓ
  let A := binary .conj (D.operationGraph f ts x) (D.operationGraph f ts y)
  have absent (w u : ℕ) (hw : w ∉ argumentVars ts) (hwu : w ≠ u) :
      w ∉ (D.operationGraph f ts u).fv := by
    intro hm
    exact (Finset.mem_insert.mp (D.fv_operationGraph_subset f ts u hm)).elim hwu hw
  have hctx (w : ℕ) (hw : w ∉ S) : w ∉ (insert A Γ).fv := by
    have h := fresh w hw
    simpa only [Context.fv_insert, hc, Finset.union_empty, A, fv_binary, Finset.mem_union, not_or]
      using And.intro (absent w x h.1 h.2.1) (absent w y h.1 h.2.2)
  have hpinputs (i : Fin n) : p ∉ (ts i).varFinset := fun hm =>
    hp'.1 (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hm⟩)
  refine ⟨Γ,hΓ,Derives.impIntro ?_⟩
  apply Derives.uniqueAt_two_values (D.operationGraph f ts p) p q (.var x) (.var y)
    (Ne.symm hq.1) (hctx p hp) (hctx q hq.2) (absent q p hq'.1 hq.1)
    (by simpa only [Term.varFinset, Finset.mem_singleton] using hp'.2.1)
    (by simpa only [Term.varFinset, Finset.mem_singleton] using hq'.2.1)
    (huniq.weaken (Finset.subset_insert A Γ))
  · rw [D.operationGraph_subst_output f ts p x hpinputs]
    exact .andLeft (.hyp Γ A)
  · rw [D.operationGraph_subst_output f ts p y hpinputs]
    exact .andRight (.hyp Γ A)

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
