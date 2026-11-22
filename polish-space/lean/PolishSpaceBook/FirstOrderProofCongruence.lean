module

public import PolishSpaceBook.FirstOrderValueBinding

@[expose] public section

/-!
# Syntactic congruence of provable equivalences

Connectives use their introduction and elimination rules. Quantification uses
an eigenvariable fresh for the context; no semantic completeness is used.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance proofCongruenceDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace AlphaFormula

/-- The usual biconditional abbreviation in the primitive natural-deduction language. -/
abbrev biimp (φ ψ : AlphaFormula L) : AlphaFormula L :=
  binary .conj (binary .imp φ ψ) (binary .imp ψ φ)

end AlphaFormula
namespace Derives

/-- Conjunction is covariant in both positions. -/
theorem conj_mono {Γ : Context L} {φ φ' ψ ψ' : AlphaFormula L}
    (hφ : Derives Γ (binary .imp φ φ')) (hψ : Derives Γ (binary .imp ψ ψ')) :
    Derives Γ (binary .imp (binary .conj φ ψ) (binary .conj φ' ψ')) := by
  apply impIntro
  exact .andIntro (.impElim (hφ.weaken (Finset.subset_insert _ _)) (.andLeft (.hyp Γ _)))
    (.impElim (hψ.weaken (Finset.subset_insert _ _)) (.andRight (.hyp Γ _)))

/-- Disjunction is covariant in both positions. -/
theorem disj_mono {Γ : Context L} {φ φ' ψ ψ' : AlphaFormula L}
    (hφ : Derives Γ (binary .imp φ φ')) (hψ : Derives Γ (binary .imp ψ ψ')) :
    Derives Γ (binary .imp (binary .disj φ ψ) (binary .disj φ' ψ')) := by
  apply impIntro
  apply orElim (.hyp Γ _)
  · exact .orLeft ψ' (.impElim (hφ.weaken (by intro θ hθ; simp [hθ])) (.hyp _ φ))
  · exact .orRight φ' (.impElim (hψ.weaken (by intro θ hθ; simp [hθ])) (.hyp _ ψ))

/-- Implication reverses its antecedent and preserves its consequent. -/
theorem imp_mono {Γ : Context L} {φ φ' ψ ψ' : AlphaFormula L}
    (hφ : Derives Γ (binary .imp φ' φ)) (hψ : Derives Γ (binary .imp ψ ψ')) :
    Derives Γ (binary .imp (binary .imp φ ψ) (binary .imp φ' ψ')) := by
  apply impIntro
  apply impIntro
  have hw : Γ ⊆ insert φ' (insert (binary .imp φ ψ) Γ) := by intro θ hθ; simp [hθ]
  exact .impElim (hψ.weaken hw)
    (.impElim (.assumption (by simp)) (.impElim (hφ.weaken hw) (.hyp _ φ')))

/-- Logical equivalences lift through every primitive binary connective. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For conjunction, transform the two components and reintroduce the conjunction. For disjunction, transform each
    branch and use disjunction elimination. For implication, transform the antecedent in the reverse direction,
    apply the given implication, and transform the consequent in the forward direction. Reverse both component
    equivalences to obtain the other implication. These are derivations under the same value assumption, so no
    existential quantifier has to be moved through a connective.
-/
theorem binary_biimp {Γ : Context L} (c : Connective) {φ φ' ψ ψ' : AlphaFormula L}
    (hφ : Derives Γ (biimp φ φ')) (hψ : Derives Γ (biimp ψ ψ')) :
    Derives Γ (biimp (binary c φ ψ) (binary c φ' ψ')) := by
  cases c with
  | conj =>
    exact .andIntro (conj_mono (.andLeft hφ) (.andLeft hψ))
      (conj_mono (.andRight hφ) (.andRight hψ))
  | disj =>
    exact .andIntro (disj_mono (.andLeft hφ) (.andLeft hψ))
      (disj_mono (.andRight hφ) (.andRight hψ))
  | imp =>
    exact .andIntro (imp_mono (.andRight hφ) (.andLeft hψ))
      (imp_mono (.andLeft hφ) (.andRight hψ))

/-- Quantification preserves implications when its name is fresh for the context. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    At a quantifier with bound variable $z$, the choice of names ensures that $z$ is different from $x,y$ and
    absent from $r$. Both substitutions therefore pass into the body. The free-variable bound for the term graph
    also gives $z\notin\FreeVarsFormula{\rho}$. For a universal quantifier, instantiate the quantified premise at
    its own bound variable, apply the appropriate direction of the body's equivalence, and universally quantify
    again. The bound name is not free in the sentence assumptions, the value graph, or the quantified premise,
    so universal introduction is valid.
    
    For an existential quantifier, open the premise at its own bound variable, apply the body's implication, and
    introduce the target existential quantifier. The bound name is absent from the free variables of the original
    context and the quantified conclusion, so existential elimination discharges the temporary body assumption.
    The same argument in reverse gives the other implication. Translation commutes with variable substitution,
    and its independence of representatives transfers the resulting conditional equivalence to the original formula.
-/
theorem quant_mono {Γ : Context L} (q : Quantifier) (x : ℕ) {φ ψ : AlphaFormula L}
    (hx : x ∉ Γ.fv) (h : Derives Γ (binary .imp φ ψ)) :
    Derives Γ (binary .imp (quant q x φ) (quant q x ψ)) := by
  cases q with
  | all =>
    apply impIntro
    apply allIntro x
    · apply impElim (h.weaken (Finset.subset_insert _ _))
      simpa only [subst_self] using Derives.allElim x φ (.var x) (.hyp Γ _)
    · simp only [Context.fv_insert,Finset.mem_union,not_or,fv_quant,Finset.notMem_erase,not_false_eq_true]
      exact ⟨trivial,hx⟩
  | ex =>
    apply impIntro
    let Δ := insert (quant .ex x φ) Γ
    have hb : Derives (insert φ Δ) (quant .ex x ψ) := by
      apply exIntro x ψ (.var x)
      rw [subst_self]
      exact .impElim (h.weaken (by intro θ hθ; simp [Δ,hθ])) (.hyp Δ φ)
    refine exElim x x φ (quant .ex x ψ) (.hyp Γ _) (by simpa only [subst_self] using hb) ?_
    simp only [Context.fv_insert,fv_quant,Finset.mem_union,Finset.mem_erase,ne_eq,not_true_eq_false,
      false_and,false_or,or_false]
    exact hx

/-- Both directions lift through a quantifier under the same eigenvariable condition. -/
theorem quant_biimp {Γ : Context L} (q : Quantifier) (x : ℕ) {φ ψ : AlphaFormula L}
    (hx : x ∉ Γ.fv) (h : Derives Γ (biimp φ ψ)) :
    Derives Γ (biimp (quant q x φ) (quant q x ψ)) :=
  .andIntro (quant_mono q x hx (.andLeft h)) (quant_mono q x hx (.andRight h))

end Derives
namespace ProvesFrom

/-- Two conditional implications give an equivalence under their shared assumption. -/
theorem conditional_biimp {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ φ ψ : AlphaFormula L)
    (hf : ProvesFrom T (binary .imp (binary .conj ρ φ) ψ))
    (hb : ProvesFrom T (binary .imp (binary .conj ρ ψ) φ)) :
    ProvesFrom T (binary .imp ρ (biimp φ ψ)) := by
  apply map₂_sentences hT hf hb
  intro Γ _ hf hb
  apply Derives.impIntro
  have forward {φ ψ : AlphaFormula L} (h : Derives Γ (binary .imp (binary .conj ρ φ) ψ)) :
      Derives (insert ρ Γ) (binary .imp φ ψ) := by
    apply Derives.impIntro
    exact .impElim (h.weaken (by intro θ hθ; simp [hθ]))
      (.andIntro (.assumption (by simp)) (.hyp _ φ))
  exact .andIntro (forward hf) (forward hb)

/-- Combine conditional equivalences without binding their shared value. -/
theorem conditional_binary {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ : AlphaFormula L) (c : Connective) {φ φ' ψ ψ' : AlphaFormula L}
    (hφ : ProvesFrom T (binary .imp ρ (biimp φ φ')))
    (hψ : ProvesFrom T (binary .imp ρ (biimp ψ ψ'))) :
    ProvesFrom T (binary .imp ρ (biimp (binary c φ ψ) (binary c φ' ψ'))) := by
  apply map₂_sentences hT hφ hψ
  intro Γ _ hφ hψ
  exact .impIntro (Derives.binary_biimp c
    (.impElim (hφ.weaken (Finset.subset_insert _ _)) (.hyp Γ ρ))
    (.impElim (hψ.weaken (Finset.subset_insert _ _)) (.hyp Γ ρ)))

/-- A bound name fresh for the shared assumption can quantify a conditional equivalence. -/
theorem conditional_quant {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ : AlphaFormula L) (q : Quantifier) (x : ℕ) {φ ψ : AlphaFormula L}
    (hx : x ∉ ρ.fv) (h : ProvesFrom T (binary .imp ρ (biimp φ ψ))) :
    ProvesFrom T (binary .imp ρ (biimp (quant q x φ) (quant q x ψ))) := by
  obtain ⟨Γ,hΓ,h⟩ := h
  refine ⟨Γ,hΓ,Derives.impIntro (Derives.quant_biimp q x ?_
    (.impElim (h.weaken (Finset.subset_insert _ _)) (.hyp Γ ρ)))⟩
  simpa only [Context.fv_insert,Context.fv_eq_empty_of_sentences hT Γ hΓ,Finset.union_empty] using hx

/-- After a conditional equivalence is established, bind the value once at the end. -/
theorem bind_conditional_biimp {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ φ ψ : AlphaFormula L) (y : ℕ) (hyφ : y ∉ φ.fv)
    (hex : ProvesFrom T (quant .ex y ρ))
    (h : ProvesFrom T (binary .imp ρ (biimp φ ψ))) :
    ProvesFrom T (biimp φ (quant .ex y (binary .conj ρ ψ))) := by
  have hf : ProvesFrom T (binary .imp (binary .conj ρ φ) ψ) := h.map (fun {Γ} h => by
    apply Derives.impIntro
    exact .impElim (.andLeft (.impElim (h.weaken (Finset.subset_insert _ _)) (.andLeft (.hyp Γ _))))
      (.andRight (.hyp Γ _)))
  have hb : ProvesFrom T (binary .imp (binary .conj ρ ψ) φ) := h.map (fun {Γ} h => by
    apply Derives.impIntro
    exact .impElim (.andRight (.impElim (h.weaken (Finset.subset_insert _ _)) (.andLeft (.hyp Γ _))))
      (.andRight (.hyp Γ _)))
  exact bind_value_equivalence hT ρ ψ φ y hyφ hex hb hf

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
