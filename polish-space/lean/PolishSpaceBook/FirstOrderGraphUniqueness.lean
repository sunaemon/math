module

public import PolishSpaceBook.FirstOrderOperationCongruence

@[expose] public section

/-!
# Unique graph values at arbitrary distinct input names

Both ordinary functions and graph-defined functions have a provable unique
output. Permutation transports their unique-existence formula to any distinct
input-output-comparison tuple, with sentence assumptions unchanged.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace AlphaFormula

theorem permute_uniqueAt (e : Equiv.Perm ℕ) (x y : ℕ) (φ : AlphaFormula L) :
    (uniqueAt x y φ).permute e = uniqueAt (e x) (e y) (φ.permute e) := by
  simp only [uniqueAt, permute_quant, permute_binary, permute_subst, permute_equal, Term.relabel]

end AlphaFormula
namespace Derives

/-- A fixed term has a unique equal value; all parameters of the term are retained. -/
theorem uniqueAt_equality {Γ : Context L} (x y : ℕ) (t : L.Term ℕ)
    (hxy : x ≠ y) (hx : x ∉ t.varFinset) (hy : y ∉ t.varFinset) (hyΓ : y ∉ Γ.fv) :
    Derives Γ (uniqueAt x y (equal (.var x) t)) := by
  have he : (equal (.var x) t).subst x (.var y) = equal (.var y) t := by
    simp only [subst_equal, termSubst_var_self, termSubst_not_free t x (.var y) hx]
  rw [uniqueAt, he]
  apply Derives.exIntro x _ t
  rw [subst_binary, subst_equal, termSubst_var_self, termSubst_not_free t x t hx,
    subst_quant_fresh .all y _ x t (Ne.symm hxy) hy, subst_binary, subst_equal, subst_equal]
  simp only [termSubst, Term.subst, ite_eq_right (Ne.symm hxy), ite_true]
  change Derives Γ (binary .conj (equal t t)
    (quant .all y (binary .imp (equal (.var y) (termSubst t x t)) (equal (.var y) t))))
  rw [termSubst_not_free t x t hx]
  exact .andIntro (.eqIntro Γ t) (.allIntro y (.impIntro (.hyp Γ _)) hyΓ)

/-- Two instances of a unique graph have equal values, by its universal characterization. -/
theorem uniqueAt_two_values {Γ : Context L} (ρ : AlphaFormula L) (x y : ℕ) (t r : L.Term ℕ)
    (hxy : x ≠ y) (hxΓ : x ∉ Γ.fv) (hyΓ : y ∉ Γ.fv) (hyρ : y ∉ ρ.fv)
    (hxt : x ∉ t.varFinset) (hyt : y ∉ t.varFinset)
    (hu : Derives Γ (uniqueAt x y ρ)) (ht : Derives Γ (ρ.subst x t))
    (hr : Derives Γ (ρ.subst x r)) : Derives Γ (equal t r) := by
  have hall := uniqueAt_specified_value ρ x y t hxy hxΓ hyΓ hyρ hxt hyt hu ht
  have hi := Derives.allElim y _ r hall
  have he : Derives Γ (equal r t) := .impElim
    (by simpa only [subst_binary, subst_equal, subst_via_fresh ρ x y r hyρ,
      termSubst_var_self, termSubst_not_free t y r hyt] using hi) hr
  exact he.eq_symm

end Derives
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Original functions use equality; defined functions use their assumed unique existence. -/
theorem proves_operationTemplate_unique {T : Set (AlphaFormula L)}
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ}
    (f : (L.sum (functionSymbols ι)).Functions n) :
    ProvesFrom T (uniqueAt n (n+1) (D.operationTemplate f)) := by
  rcases f with f | f
  · let t : L.Term ℕ := .func f (fun i : Fin n => .var i.val)
    have ht (x : ℕ) (hx : n ≤ x) : x ∉ t.varFinset := by
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
      have he : x = i.val := by simpa using hi
      have := i.isLt
      omega
    exact ⟨∅, by simp, Derives.uniqueAt_equality n (n+1) t (by omega)
      (ht n (by omega)) (ht (n+1) (by omega)) (by simp [Context.fv])⟩
  · exact (hu n f).map (Derives.open_closeAll n _)

/-- A function graph has a unique output at any pairwise distinct named inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Each operation graph has a provably unique output at distinct named inputs. For an old function, its value term
    supplies existence; two values equal to that term are equal by symmetry and transitivity. For a defined function,
    instantiate the universal unique-existence axiom at its original inputs. Extend the finite correspondence of
    input, output, and comparison names to a permutation, and rename the derivation. The graph is the desired
    simultaneous instance, and sentence assumptions are unchanged. Symmetry and transitivity for open terms follow
    from the same equality-elimination proofs given earlier, choosing the hole fresh for the fixed terms.
-/
theorem proves_operationGraph_unique {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ}
    (f : (L.sum (functionSymbols ι)).Functions n) (a : Fin n → ℕ) (ha : Function.Injective a)
    (x y : ℕ) (hxy : x ≠ y) (hx : x ∉ Set.range a) (hy : y ∉ Set.range a) :
    ProvesFrom T (uniqueAt x y (D.operationGraph f (fun i => .var (a i)) x)) := by
  let b : Fin (n+1) → ℕ := Fin.snoc a x
  have hb : Function.Injective b := Fin.snoc_injective_of_injective ha hx
  have hyb : y ∉ Set.range b := by
    rintro ⟨i,hi⟩
    cases i using Fin.lastCases with
    | last => exact hxy (by simpa [b] using hi)
    | cast i => exact hy ⟨i,by simpa [b] using hi⟩
  let c : Fin (n+2) → ℕ := Fin.snoc b y
  have hc : Function.Injective c := Fin.snoc_injective_of_injective hb hyb
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin (n+2) => i.val) c Fin.val_injective hc
  have hex : e n = x := by simpa [c,b] using he (Fin.last n).castSucc
  have hey : e (n+1) = y := by simpa [c] using he (Fin.last (n+1))
  have hargs : (fun i : Fin (n+1) => (Term.var (e i.val) : L.Term ℕ)) =
      Fin.snoc (α := fun _ => L.Term ℕ) (fun i => .var (a i)) (.var x) := by
    funext i
    cases i using Fin.lastCases with
    | last => simp only [Fin.val_last, hex, Fin.snoc_last]
    | cast i => simpa [c,b] using congrArg (Term.var (L := L)) (he i.castSucc.castSucc)
  obtain ⟨Γ,hΓ,h⟩ := D.proves_operationTemplate_unique hu f
  have hp := h.permute_sentence_context (Context.fv_eq_empty_of_sentences hT Γ hΓ) e
  rw [permute_uniqueAt, hex, hey, ← simultaneous_permutation _ e (D.fv_operationTemplate f),
    hargs, ← D.operationGraph_eq_instance] at hp
  exact ⟨Γ,hΓ,hp⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
