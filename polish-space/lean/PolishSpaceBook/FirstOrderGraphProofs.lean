module

public import PolishSpaceBook.FirstOrderFunctionClasses

@[expose] public section

/-!
# Graph witnesses inside natural-deduction proofs

This is the proof-theoretic single-witness step. The premises are derivations
of the specified graph value and of its uniqueness. Existential elimination
and equality elimination construct both directions explicitly.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

namespace AlphaFormula

theorem not_mem_fv_subst_self (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ)
    (ht : x ∉ t.varFinset) : x ∉ (φ.subst x t).fv := by
  rw [fv_subst]
  simp only [Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, false_or]
  split_ifs <;> simp_all

/-- Instantiation can pass through a fresh name, by the earlier bound-name theorem. -/
theorem subst_via_fresh (φ : AlphaFormula L) (x z : ℕ) (t : L.Term ℕ) (hz : z ∉ φ.fv) :
    (φ.subst x (.var z)).subst z t = φ.subst x t := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Quotient.sound ((Formula.Alpha.rename .all φ x z hz).instantiate t).symm

theorem quant_rename (q : Quantifier) (φ : AlphaFormula L) (x z : ℕ) (hz : z ∉ φ.fv) :
    quant q x φ = quant q z (φ.subst x (.var z)) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Quotient.sound (Formula.Alpha.rename q φ x z hz)

end AlphaFormula
namespace Derives

/-- Introducing the specified graph value is conjunction introduction followed by existential introduction. -/
theorem graph_witness_intro {Γ : Context L} (ρ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ)
    (hvalue : Derives Γ (ρ.subst x t)) (hψ : Derives Γ (ψ.subst x t)) :
    Derives Γ (quant .ex x (binary .conj ρ ψ)) :=
  .exIntro x _ t (by simpa only [subst_binary] using Derives.andIntro hvalue hψ)

/-- The eigenvariable can be the graph variable itself because substitution removes it from the conclusion. -/
theorem graph_witness_elim {Γ : Context L} (ρ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ)
    (hx : x ∉ Γ.fv) (ht : x ∉ t.varFinset)
    (hbound : Derives Γ (quant .all x (binary .imp ρ (equal (.var x) t))))
    (hex : Derives Γ (quant .ex x (binary .conj ρ ψ))) : Derives Γ (ψ.subst x t) := by
  have hb : Derives (insert (binary .conj ρ ψ) Γ)
      (quant .all x (binary .imp ρ (equal (.var x) t))) := hbound.weaken (Finset.subset_insert _ _)
  have hbody := Derives.hyp Γ (binary .conj ρ ψ)
  have heq : Derives (insert (binary .conj ρ ψ) Γ) (equal (.var x) t) :=
    .impElim (by simpa only [subst_self] using Derives.allElim x _ (.var x) hb) (.andLeft hbody)
  have hc : Derives (insert (binary .conj ρ ψ) Γ) (ψ.subst x t) :=
    .eqElim ψ x (.var x) t (by simpa only [subst_self] using Derives.andRight hbody) heq
  apply Derives.exElim x x (binary .conj ρ ψ) (ψ.subst x t) hex
    (by simpa only [subst_self] using hc)
  have hψ := not_mem_fv_subst_self ψ x t ht
  simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
    false_and, or_false, not_or]
  exact ⟨hx,hψ⟩

/-- Both implications of graph replacement are derivable under the original context. -/
theorem graph_witness_equivalence {Γ : Context L} (ρ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ)
    (hx : x ∉ Γ.fv) (ht : x ∉ t.varFinset)
    (hvalue : Derives Γ (ρ.subst x t))
    (hbound : Derives Γ (quant .all x (binary .imp ρ (equal (.var x) t)))) :
    Derives Γ (binary .conj
      (binary .imp (ψ.subst x t) (quant .ex x (binary .conj ρ ψ)))
      (binary .imp (quant .ex x (binary .conj ρ ψ)) (ψ.subst x t))) := by
  apply Derives.andIntro
  · apply Derives.impIntro
    exact graph_witness_intro ρ ψ x t (hvalue.weaken (Finset.subset_insert _ _)) (.hyp Γ _)
  · apply Derives.impIntro
    apply graph_witness_elim ρ ψ x t _ ht (hbound.weaken (Finset.subset_insert _ _)) (.hyp Γ _)
    simpa only [Context.fv_insert, fv_quant, Finset.mem_union, Finset.mem_erase, ne_eq,
      not_true_eq_false, false_and, false_or] using hx

/-- Equality is the graph of a specified term, including terms with parameters. -/
theorem equality_witness {Γ : Context L} (ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ)
    (hx : x ∉ Γ.fv) (ht : x ∉ t.varFinset) :
    Derives Γ (binary .conj
      (binary .imp (ψ.subst x t) (quant .ex x (binary .conj (equal (.var x) t) ψ)))
      (binary .imp (quant .ex x (binary .conj (equal (.var x) t) ψ)) (ψ.subst x t))) := by
  apply graph_witness_equivalence _ ψ x t hx ht
  · simpa only [subst_equal, termSubst_var_self, termSubst_not_free t x t ht] using Derives.eqIntro Γ t
  · exact .allIntro x (.impIntro (.hyp Γ _)) hx

end Derives
namespace ProvesFrom

/-- Combine two finite proofs while retaining the empty free-variable set of sentence assumptions. -/
theorem map₂_sentences {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    {φ ψ χ : AlphaFormula L} (hφ : ProvesFrom T φ) (hψ : ProvesFrom T ψ)
    (f : ∀ {Γ : Context L}, Γ.fv = ∅ → Derives Γ φ → Derives Γ ψ → Derives Γ χ) : ProvesFrom T χ := by
  obtain ⟨Γ,hΓ,hdφ⟩ := hφ
  obtain ⟨Δ,hΔ,hdψ⟩ := hψ
  have hctx : ∀ θ ∈ Γ ∪ Δ, θ ∈ T := by
    intro θ hθ; exact (Finset.mem_union.mp hθ).elim (hΓ θ) (hΔ θ)
  exact ⟨Γ ∪ Δ,hctx,f (Context.fv_eq_empty_of_sentences hT _ hctx)
    (hdφ.weaken Finset.subset_union_left) (hdψ.weaken Finset.subset_union_right)⟩

/-- Sentence assumptions provide the eigenvariable condition for the proof-theoretic graph step. -/
theorem graph_witness_equivalence {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) (ht : x ∉ t.varFinset)
    (hvalue : ProvesFrom T (ρ.subst x t))
    (hbound : ProvesFrom T (quant .all x (binary .imp ρ (equal (.var x) t)))) :
    ProvesFrom T (binary .conj
      (binary .imp (ψ.subst x t) (quant .ex x (binary .conj ρ ψ)))
      (binary .imp (quant .ex x (binary .conj ρ ψ)) (ψ.subst x t))) := by
  apply map₂_sentences hT hvalue hbound
  intro Γ hΓ hv hb
  exact Derives.graph_witness_equivalence ρ ψ x t (by rw [hΓ]; simp) ht hv hb

theorem graph_witness_iff {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) (ht : x ∉ t.varFinset)
    (hvalue : ProvesFrom T (ρ.subst x t))
    (hbound : ProvesFrom T (quant .all x (binary .imp ρ (equal (.var x) t)))) :
    ProvesFrom T (ψ.subst x t) ↔ ProvesFrom T (quant .ex x (binary .conj ρ ψ)) := by
  have h := graph_witness_equivalence hT ρ ψ x t ht hvalue hbound
  exact ⟨fun hψ => (h.map Derives.andLeft).impElim hψ,
    fun hex => (h.map Derives.andRight).impElim hex⟩

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
