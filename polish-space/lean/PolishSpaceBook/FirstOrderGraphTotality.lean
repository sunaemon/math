module

public import PolishSpaceBook.FirstOrderWitnessBlocks
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-!
# Derivable totality of operation graphs

Instantiate the closed unique-existence axiom at its original names, project
existence, and rename the finite input-output tuple by a permutation. A
simultaneous substitution agrees with that permutation on its supported names.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

namespace AlphaFormula

/-- A simultaneous substitution by a permutation agrees with renaming all names. -/
theorem simultaneous_permutation {n : ℕ} (φ : AlphaFormula L) (e : Equiv.Perm ℕ)
    (hf : φ.fv ⊆ Finset.range n) :
    φ.simultaneous (fun i : Fin n => .var (e i.val)) = φ.permute e := by
  have h := simultaneous_corresponds φ (fun i : Fin n => .var i.val)
    (fun i => .var (e i.val)) (fun a b => b = e a) hf (fun _ => .var rfl)
  rw [simultaneous_vars] at h
  rcases h with ⟨a,b,ha,hb,h⟩
  have hh := h.permute e (Equiv.refl ℕ) (S := Eq) (fun _ _ he => he.symm)
  have he : mk (a.permute e) = mk b := by
    apply Quotient.sound
    change Formula.Alpha (a.permute e) b
    simpa only [Formula.permute_id] using hh.eq_alpha
  simpa only [← permute_mk, ha, hb] using he.symm

end AlphaFormula
namespace Derives

/-- Universal closure can be instantiated at its own variable names. -/
theorem open_closeAll {Γ : Context L} (n : ℕ) (φ : AlphaFormula L)
    (h : Derives Γ (closeAll n φ)) : Derives Γ φ := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (by simpa only [subst_self] using allElim n _ (.var n) h)

/-- Project existence from the expanded unique-existence formula. -/
theorem uniqueAt_exists {Γ : Context L} (φ : AlphaFormula L) (x w : ℕ)
    (hx : x ∉ Γ.fv) (h : Derives Γ (uniqueAt x w φ)) : Derives Γ (quant .ex x φ) := by
  let U := binary .conj φ (quant .all w (binary .imp (φ.subst x (.var w)) (equal (.var w) (.var x))))
  apply Derives.exElim x x U (quant .ex x φ) h
  · simpa only [subst_self] using Derives.exIntro x φ (.var x)
      (by simpa only [subst_self] using Derives.andLeft (Derives.hyp Γ U))
  · simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, or_false]
    exact hx

/-- Sentence assumptions are fixed by every permutation of variable names. -/
theorem permute_sentence_context {Γ : Context L} (hΓ : Γ.fv = ∅) {φ : AlphaFormula L}
    (h : Derives Γ φ) (e : Equiv.Perm ℕ) : Derives Γ (φ.permute e) := by
  apply h.permute_weaken e Γ
  intro ψ hψ
  rw [permute_fixed ψ e (fun x hx => False.elim (by
    have hm := Context.mem_fv_of_mem hψ hx
    simp only [hΓ, Finset.notMem_empty] at hm))]
  exact hψ

end Derives
namespace ProvesFrom

/-- Finitely many theory proofs have a proof of their conjunction. -/
theorem conjoin {T : Set (AlphaFormula L)} (n : ℕ) (φ : Fin n → AlphaFormula L)
    (h : ∀ i, ProvesFrom T (φ i)) : ProvesFrom T (AlphaFormula.conjoin n φ) := by
  induction n with
  | zero => exact ⟨∅, by simp, .impIntro (.hyp ∅ falsum)⟩
  | succ n ih => exact (h 0).map₂ (ih _ (fun i => h i.succ)) (fun h₀ h₁ => .andIntro h₀ h₁)

end ProvesFrom
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- At named inputs, the unique-existence axioms give an operation graph value in the old language. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    First derive $T\vdash\exists y\,\FirstOrderOperationGraph{f}{\vec{z}}{y}$ at the input names $z_i=v_{B+i}$
    and an output name whose index is below $B$. For an old function, use the term $f(\vec{z})$ as witness and
    equality reflexivity. For a defined function, instantiate the universal closure of its unique-existence
    hypothesis at its original input variables and discard the uniqueness conjunct under existential elimination.
    The resulting existential formula can be renamed to the desired inputs and output: their names are distinct,
    so the finite bijection extends to a permutation by pairing the remaining names in the union of its domain and
    range. Apply the renaming rule to the derivation. The assumptions from $T$ are sentences and hence are fixed
    as $\alpha$-classes. Comparison of simultaneous instances identifies the renamed defining graph with the required
    operation graph.
-/
theorem proves_operationGraph_exists {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ}
    (f : (L.sum (functionSymbols ι)).Functions n) (B x : ℕ) (hx : x < B) :
    ProvesFrom T (quant .ex x (D.operationGraph f (fun i => .var (B+i.val)) x)) := by
  rcases f with f | f
  · let t : L.Term ℕ := .func f (fun i : Fin n => .var (B+i.val))
    have ht : x ∉ t.varFinset := by
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
      have he : x = B+i.val := by simpa using hi
      omega
    refine ⟨∅, by simp, Derives.exIntro x _ t ?_⟩
    change Derives ∅ ((equal (.var x) t).subst x t)
    simpa only [subst_equal, termSubst_var_self, termSubst_not_free t x t ht]
      using Derives.eqIntro (∅ : Context L) t
  · let a : Fin (n+1) → ℕ := Fin.snoc (fun i : Fin n => B+i.val) x
    have hi : Function.Injective a := by
      intro i j he
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => rfl
        | cast j =>
          have h : x = B+j.val := by simpa [a] using he
          omega
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          have h : B+i.val = x := by simpa [a] using he
          omega
        | cast j =>
          have h : B+i.val = B+j.val := by simpa [a] using he
          congr 1
          exact Fin.ext (by omega)
    obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin (n+1) => i.val) a Fin.val_injective hi
    have hout : e n = x := by simpa [a] using he (Fin.last n)
    have hargs : (fun i : Fin (n+1) => (Term.var (e i.val) : L.Term ℕ)) =
        Fin.snoc (α := fun _ => L.Term ℕ) (fun i : Fin n => .var (B+i.val)) (.var x) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp only [Fin.val_last, hout, Fin.snoc_last]
      | cast i => simpa [a] using congrArg (Term.var (L := L)) (he i.castSucc)
    obtain ⟨Γ,hΓ,h⟩ := hu n f
    have hc := Context.fv_eq_empty_of_sentences hT Γ hΓ
    have hg := Derives.uniqueAt_exists (D.graph f) n (n+1) (by rw [hc]; simp)
      (Derives.open_closeAll n _ h)
    have hp := hg.permute_sentence_context hc e
    rw [permute_quant, hout, ← simultaneous_permutation (D.graph f) e (D.freeVars f), hargs] at hp
    exact ⟨Γ,hΓ,hp⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
