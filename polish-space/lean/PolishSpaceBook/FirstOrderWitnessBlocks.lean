module

public import PolishSpaceBook.FirstOrderUniqueGraphProofs

@[expose] public section

/-!
# Independent finite families of existential witnesses

The proof opens one witness at a time. Cross-freshness keeps every later
existential elimination valid in the enlarged context.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace Derives

/-- Assemble finitely many conjunction components, including the empty case. -/
theorem conjoin_intro {Γ : Context L} (n : ℕ) (φ : Fin n → AlphaFormula L)
    (h : ∀ i, Derives Γ (φ i)) : Derives Γ (conjoin n φ) := by
  induction n with
  | zero => exact .impIntro (.hyp Γ falsum)
  | succ n ih => exact .andIntro (h 0) (ih _ (fun i => h i.succ))

/-- Extract a specified component of a finite conjunction. -/
theorem conjoin_elim {Γ : Context L} (n : ℕ) (φ : Fin n → AlphaFormula L)
    (h : Derives Γ (conjoin n φ)) (i : Fin n) : Derives Γ (φ i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    exact Fin.cases (.andLeft h) (fun j => ih _ (.andRight h) j) i

/-- Bind a block using its own variable names as the witnesses. -/
theorem existsBlock_intro_self {Γ : Context L} (n B : ℕ) (φ : AlphaFormula L)
    (h : Derives Γ φ) : Derives Γ (existsBlock n B φ) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact .exIntro (B+n) _ (.var (B+n)) (by simpa only [subst_self] using ih)

/-- Eliminate a block whose names are absent from the context and final conclusion. -/
theorem existsBlock_elim_self {Γ : Context L} (n B : ℕ) (φ χ : AlphaFormula L)
    (hΓ : ∀ i : Fin n, B+i.val ∉ Γ.fv) (hχ : ∀ i : Fin n, B+i.val ∉ χ.fv)
    (hex : Derives Γ (existsBlock n B φ)) (hbody : Derives (insert φ Γ) χ) : Derives Γ χ := by
  induction n generalizing Γ with
  | zero =>
    exact hbody.cut (fun θ hθ => (Finset.mem_insert.mp hθ).elim
      (fun he => he ▸ hex) (fun hθ => .assumption hθ))
  | succ n ih =>
    let E := existsBlock n B φ
    have hi : Derives (insert E Γ) χ := by
      apply ih (fun i => ?_) (fun i => hχ i.castSucc) (.hyp Γ E)
      · apply hbody.weaken
        intro θ hθ
        simp only [Finset.mem_insert] at *
        tauto
      · rw [Context.fv_insert, Finset.mem_union, not_or]
        refine ⟨?_,hΓ i.castSucc⟩
        change B+i.val ∉ (existsBlock n B φ).fv
        rw [fv_existsBlock, Finset.mem_sdiff]
        exact fun h => h.2 ((mem_temporaryNames_iff n B _).mpr ⟨by omega, by have := i.isLt; omega⟩)
    apply Derives.exElim (B+n) (B+n) E χ hex (by simpa only [subst_self] using hi)
    simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, or_false, not_or]
    exact ⟨hΓ (Fin.last n), hχ (Fin.last n)⟩

/-- Open independent witnesses while retaining the original assumptions and conclusion. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    We use a finite witness argument. Suppose $\Gamma\vdash\exists z_i\,\rho_i$ for each $i<n$, the names
    $z_i$ are distinct and absent from the free variables of $\Gamma$ and $\chi$, and $z_i$ is not free in
    $\rho_j$ when $i\ne j$. If $\Gamma,\bigwedge_{i<n}\rho_i\vdash\chi$, then $\Gamma\vdash\chi$.
    To see this, open the existential assumptions one at a time and combine their bodies by conjunction introduction.
    Each later witness name remains fresh for every earlier body by the cross-freshness condition.
    Use the given derivation of the conclusion, then discharge the temporary assumptions by existential elimination.
    For an empty family, the conjunction is true and has a proof without assumptions.
-/
theorem independent_witnesses {Γ : Context L} (n B : ℕ) (ρ : Fin n → AlphaFormula L)
    (χ : AlphaFormula L) (hΓ : ∀ i : Fin n, B+i.val ∉ Γ.fv)
    (hχ : ∀ i : Fin n, B+i.val ∉ χ.fv)
    (hcross : ∀ i j : Fin n, i ≠ j → B+i.val ∉ (ρ j).fv)
    (hex : ∀ i, Derives Γ (quant .ex (B+i.val) (ρ i)))
    (hbody : Derives (insert (conjoin n ρ) Γ) χ) : Derives Γ χ := by
  induction n generalizing B Γ with
  | zero =>
    apply hbody.cut
    intro θ hθ
    rcases Finset.mem_insert.mp hθ with rfl | hθ
    · exact conjoin_intro 0 ρ (fun i => Fin.elim0 i)
    · exact .assumption hθ
  | succ n ih =>
    have he (i : Fin n) : B+1+i.val = B+i.succ.val := by simp only [Fin.val_succ]; omega
    have hi : Derives (insert (ρ 0) Γ) χ := by
      apply ih (B+1) (fun i => ρ i.succ)
      · intro i
        rw [Context.fv_insert, Finset.mem_union, not_or]
        rw [he]
        exact ⟨hcross i.succ 0 (Fin.succ_ne_zero i), hΓ i.succ⟩
      · intro i
        simpa only [he] using hχ i.succ
      · intro i j hij
        simpa only [he] using hcross i.succ j.succ (by simpa using hij)
      · intro i
        simpa only [he] using (hex i.succ).weaken (Finset.subset_insert (ρ 0) Γ)
      · apply hbody.cut
        intro θ hθ
        rcases Finset.mem_insert.mp hθ with rfl | hθ
        · exact .andIntro (.assumption (by simp)) (.hyp _ _)
        · exact .assumption (by simp [hθ])
    apply Derives.exElim B B (ρ 0) χ (by simpa using hex 0) (by simpa only [subst_self] using hi)
    simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, or_false, not_or]
    exact ⟨by simpa using hΓ 0, by simpa using hχ 0⟩

/-- Individually existing independent witnesses can be assembled in one bound block. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    In particular, the bodies together imply their existentially quantified conjunction by using their own variable
    names as witnesses, so the individual existence proofs give a proof of that quantified conjunction.
-/
theorem independent_witness_block {Γ : Context L} (n B : ℕ) (ρ : Fin n → AlphaFormula L)
    (hΓ : ∀ i : Fin n, B+i.val ∉ Γ.fv)
    (hcross : ∀ i j : Fin n, i ≠ j → B+i.val ∉ (ρ j).fv)
    (hex : ∀ i, Derives Γ (quant .ex (B+i.val) (ρ i))) :
    Derives Γ (existsBlock n B (conjoin n ρ)) := by
  refine independent_witnesses n B ρ _ hΓ ?_ hcross hex ?_
  · intro i
    rw [fv_existsBlock, Finset.mem_sdiff]
    exact fun h => h.2 ((mem_temporaryNames_iff n B _).mpr ⟨by omega, by have := i.isLt; omega⟩)
  · exact existsBlock_intro_self n B _ (.hyp Γ _)

end Derives
end PolishSpaceBook.NamedFirstOrder
