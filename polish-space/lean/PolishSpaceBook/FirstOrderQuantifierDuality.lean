module

public import PolishSpaceBook.FirstOrderMaximalConnectives

@[expose] public section

/-!
# Syntactic duality of the universal and existential quantifiers

Identity substitution and substitution through negation are established before
deriving the duality from natural deduction. Sentence hypotheses permit the
bound variable itself as eigenvariable; no model-existence argument is used.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

@[simp] theorem termSubst_self (t : L.Term ℕ) (x : ℕ) : termSubst t x (.var x) = t := by
  induction t with
  | var y => by_cases h : y = x <;> simp [termSubst, Term.subst, h]
  | func f ts ih => simp only [termSubst_func, ih]

@[simp] theorem Formula.subst_self (φ : Formula L) (x : ℕ) : φ.subst x (.var x) = φ := by
  induction φ with
  | falsum => rfl
  | equal t r => simp only [Formula.subst_equal, termSubst_self]
  | rel R ts => simp only [Formula.subst_rel, termSubst_self]
  | binary c φ ψ ihφ ihψ => simp only [Formula.subst_binary, ihφ, ihψ]
  | quant q y φ ih => by_cases h : y = x <;> simp [Formula.subst_quant, h, Term.varFinset, ih]

namespace AlphaFormula

@[simp] theorem subst_falsum (x : ℕ) (t : L.Term ℕ) : (falsum : AlphaFormula L).subst x t = falsum := rfl

@[simp] theorem subst_binary (c : Connective) (φ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
    (binary c φ ψ).subst x t = binary c (φ.subst x t) (ψ.subst x t) := by
  induction φ, ψ using Quotient.inductionOn₂ with
  | _ φ ψ => exact congrArg mk (Formula.subst_binary c φ ψ x t)

@[simp] theorem subst_neg (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
    (neg φ).subst x t = neg (φ.subst x t) := by simp [neg]

@[simp] theorem subst_self (φ : AlphaFormula L) (x : ℕ) : φ.subst x (.var x) = φ := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (Formula.subst_self φ x)

end AlphaFormula

namespace Context

@[simp] theorem fv_insert (Γ : Context L) (φ : AlphaFormula L) : (insert φ Γ).fv = φ.fv ∪ Γ.fv :=
  Finset.biUnion_insert

theorem fv_eq_empty_of_sentences {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (Γ : Context L) (hΓ : ∀ φ ∈ Γ, φ ∈ T) : Γ.fv = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨φ, hφ, hx⟩ := Finset.mem_biUnion.mp hx
  have hf : φ.fv = ∅ := hT (hΓ φ hφ)
  simp [hf] at hx

end Context

namespace ProvesFrom

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the converse, first derive the equivalence of $\forallbind{x}{\varphi}$ and
    $\neg\existsbind{x}{\neg\varphi}$ in the deduction system. Universal elimination and existential elimination
    make the first formula incompatible with $\existsbind{x}{\neg\varphi}$. In the other direction, under the
    assumption $\neg\existsbind{x}{\neg\varphi}$, an additional assumption $\neg\varphi$ gives
    $\existsbind{x}{\neg\varphi}$ by existential introduction. Double-negation elimination gives $\varphi$;
    universal introduction then gives $\forallbind{x}{\varphi}$. The undischarged assumptions are sentences,
    so the eigenvariable conditions hold.
-/
theorem all_iff_not_ex_not {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (x : ℕ) (φ : AlphaFormula L) :
    ProvesFrom T (quant .all x φ) ↔ ProvesFrom T (neg (quant .ex x (neg φ))) := by
  constructor
  · rintro ⟨Γ, hΓ, hd⟩
    have hFV := Context.fv_eq_empty_of_sentences hT Γ hΓ
    refine ⟨Γ, hΓ, .negIntro ?_⟩
    apply Derives.exElim x x (neg φ) falsum (.hyp Γ (quant .ex x (neg φ)))
    · have ha : Derives (insert ((neg φ).subst x (.var x)) (insert (quant .ex x (neg φ)) Γ))
          (φ.subst x (.var x)) := Derives.allElim x φ (.var x)
        ((hd.weaken (Finset.subset_insert _ _)).weaken (Finset.subset_insert _ _))
      have hn := Derives.hyp (insert (quant .ex x (neg φ)) Γ) ((neg φ).subst x (.var x))
      exact .impElim (by simpa only [neg, subst_binary, subst_falsum] using hn) ha
    · simp [hFV, fv_quant]
  · rintro ⟨Γ, hΓ, hd⟩
    have hFV := Context.fv_eq_empty_of_sentences hT Γ hΓ
    refine ⟨Γ, hΓ, .allIntro x ?_ (by simp [hFV])⟩
    apply Derives.doubleNegElim
    apply Derives.negIntro
    apply Derives.impElim (hd.weaken (Finset.subset_insert _ _))
    exact .exIntro x (neg φ) (.var x) (by simpa only [subst_self] using Derives.hyp Γ (neg φ))

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
