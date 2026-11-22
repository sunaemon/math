module

public import PolishSpaceBook.FirstOrderInstanceCongruence

@[expose] public section

/-!
# Equality transport for operation graphs

Old functions and newly defined functions are instances of one formula with
input slots followed by an output slot. Equal values transport the whole graph.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace AlphaFormula

/-- An atomic equality has no bound names, so simultaneous substitution is literal. -/
theorem simultaneous_equal {n : ℕ} (t r : L.Term ℕ) (ts : Fin n → L.Term ℕ) :
    (equal t r).simultaneous ts =
      equal (t.subst (fun x => if h : x < n then ts ⟨x,h⟩ else .var x))
        (r.subst (fun x => if h : x < n then ts ⟨x,h⟩ else .var x)) := by
  have hb := substitutionBound_spec (equal t r) ts
  change (mk (.equal t r)).simultaneousAt ts ((equal t r).substitutionBound ts) = _
  rw [simultaneousAt_mk_literal _ _ _ hb.1 hb.2.1 hb.2.2 (by simp [Formula.boundNames])]
  rfl

end AlphaFormula
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Use the first slots for inputs and the last slot for the output. -/
def operationTemplate {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n) : AlphaFormula L :=
  match f with
  | Sum.inl g => equal (.var n) (.func g (fun i => .var i.val))
  | Sum.inr g => D.graph g

theorem fv_operationTemplate {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n) :
    (D.operationTemplate f).fv ⊆ Finset.range (n+1) := by
  rcases f with f | f
  · intro x hx
    change x ∈ ({n} ∪ Finset.univ.biUnion (fun i : Fin n => ({i.val} : Finset ℕ))) at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have he : x = n := Finset.mem_singleton.mp hx
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
      have he : x = i.val := Finset.mem_singleton.mp hi
      exact Finset.mem_range.mpr (by have := i.isLt; omega)
  · exact D.freeVars f

theorem operationGraph_eq_instance {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts : Fin n → L.Term ℕ) (x : ℕ) :
    D.operationGraph f ts x =
      (D.operationTemplate f).simultaneous (Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x)) := by
  rcases f with f | f
  · rw [operationTemplate, simultaneous_equal]
    simp only [Term.subst, Nat.lt_succ_self, dite_eq_left]
    have ho : Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x) ⟨n,Nat.lt_succ_self n⟩ = .var x :=
      Fin.snoc_last (α := fun _ => L.Term ℕ) (.var x) ts
    rw [ho]
    change equal (.var x) (.func f ts) = equal (.var x)
      (.func f (fun i : Fin n => if h : i.val < n+1 then Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x) ⟨i.val,h⟩ else .var i.val))
    congr 2
    funext i
    have hi : i.val < n+1 := by have := i.isLt; omega
    simp only [dite_eq_left hi]
    exact (Fin.snoc_castSucc (α := fun _ => L.Term ℕ) (.var x) ts i).symm
  · rfl

/-- Pointwise equal arguments and outputs preserve the operation's graph constraint. -/
theorem derives_operationGraph_congr {Γ : Context L} {n : ℕ}
    (f : (L.sum (functionSymbols ι)).Functions n) (ts us : Fin n → L.Term ℕ) (x y : ℕ)
    (hargs : ∀ i, Derives Γ (equal (ts i) (us i)))
    (hout : Derives Γ (equal (.var x) (.var y))) (h : Derives Γ (D.operationGraph f ts x)) :
    Derives Γ (D.operationGraph f us y) := by
  rw [D.operationGraph_eq_instance] at h ⊢
  apply Derives.simultaneous_congr _ (D.fv_operationTemplate f) _ _ _ h
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hout
  | cast i => simpa only [Fin.snoc_castSucc] using hargs i

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
