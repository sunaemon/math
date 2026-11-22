module

public import PolishSpaceBook.FirstOrderTermGraphComposition

@[expose] public section

/-!
# Transfer through a block of argument values

Transform each child graph and retain the same continuation on those values.
Freshness for the shared assumption and conclusion permits the witness block
to be opened and rebound without changing any original parameter.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance argumentGraphTransferDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- An atomic continuation leaves only the original argument parameters free. -/
theorem withValues_fv_below {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (B : ℕ) (ψ : AlphaFormula L) (hψ : ψ.fv ⊆ temporaryNames n B)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) :
    ∀ a ∈ (D.withValues ts B ψ).fv, a < B := by
  intro a ha
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (D.fv_withValues_atom ts B ψ hψ ha)
  exact ht i a hi

/-- Pointwise implications between argument graphs lift through their existential block. -/
theorem derives_withValues_map {Γ : Context L} {n : ℕ}
    (ts us : Fin n → (L.sum (functionSymbols ι)).Term ℕ) (B : ℕ) (ψ : AlphaFormula L)
    (hΓ : ∀ a ∈ Γ.fv, a < B) (hψ : ψ.fv ⊆ temporaryNames n B)
    (hu : ∀ i a, a ∈ (us i).varFinset → a < B)
    (hP : ∀ i, Derives Γ (binary .imp (D.termGraph (ts i) (B+i.val) (B+n))
      (D.termGraph (us i) (B+i.val) (B+n))))
    (h : Derives Γ (D.withValues ts B ψ)) : Derives Γ (D.withValues us B ψ) := by
  let M := binary .conj (conjoin n (fun i => D.termGraph (ts i) (B+i.val) (B+n))) ψ
  let N := binary .conj (conjoin n (fun i => D.termGraph (us i) (B+i.val) (B+n))) ψ
  have hb : Derives (insert M Γ) (D.withValues us B ψ) := by
    apply Derives.existsBlock_intro_self n B N
    apply Derives.andIntro _ (.andRight (.hyp Γ M))
    apply Derives.conjoin_intro
    intro i
    exact .impElim ((hP i).weaken (Finset.subset_insert _ _))
      (Derives.conjoin_elim n _ (.andLeft (.hyp Γ M)) i)
  exact Derives.existsBlock_elim_self n B M _
    (fun i hm => by have := hΓ _ hm; omega)
    (fun i hm => by have := D.withValues_fv_below us B ψ hψ hu _ hm; omega) h hb

/-- Lift argument implications proved under one shared value assumption. -/
theorem proves_withValues_map {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L) {n : ℕ}
    (ts us : Fin n → (L.sum (functionSymbols ι)).Term ℕ) (B : ℕ) (ρ ψ : AlphaFormula L)
    (hρ : ∀ a ∈ ρ.fv, a < B) (hψ : ψ.fv ⊆ temporaryNames n B)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B)
    (hu : ∀ i a, a ∈ (us i).varFinset → a < B)
    (hP : ∀ i, ProvesFrom T (binary .imp
      (binary .conj ρ (D.termGraph (ts i) (B+i.val) (B+n)))
      (D.termGraph (us i) (B+i.val) (B+n)))) :
    ProvesFrom T (binary .imp (binary .conj ρ (D.withValues ts B ψ)) (D.withValues us B ψ)) := by
  let P (i : Fin n) := binary .imp (binary .conj ρ (D.termGraph (ts i) (B+i.val) (B+n)))
    (D.termGraph (us i) (B+i.val) (B+n))
  obtain ⟨Γ,hΓ,hPs⟩ := ProvesFrom.conjoin n P hP
  have hΓfv := Context.fv_eq_empty_of_sentences hT Γ hΓ
  let A := binary .conj ρ (D.withValues ts B ψ)
  let Δ := insert A Γ
  have hΔ (a : ℕ) (ha : a ∈ Δ.fv) : a < B := by
    simp only [Δ,Context.fv_insert,hΓfv,Finset.union_empty,A,fv_binary,Finset.mem_union] at ha
    exact ha.elim (hρ a) (D.withValues_fv_below ts B ψ hψ ht a)
  have hm (i : Fin n) : Derives Δ (binary .imp (D.termGraph (ts i) (B+i.val) (B+n))
      (D.termGraph (us i) (B+i.val) (B+n))) := by
    apply Derives.impIntro
    have hwΓ : Γ ⊆ insert (D.termGraph (ts i) (B+i.val) (B+n)) Δ := by
      intro φ hφ; simp [Δ,hφ]
    apply Derives.impElim ((Derives.conjoin_elim n P hPs i).weaken hwΓ)
    exact .andIntro (.andLeft (.assumption (φ := A) (by simp [Δ]))) (.hyp Δ _)
  exact ⟨Γ,hΓ,Derives.impIntro (D.derives_withValues_map ts us B ψ hΔ hψ hu hm (.andRight (.hyp Γ A)))⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
