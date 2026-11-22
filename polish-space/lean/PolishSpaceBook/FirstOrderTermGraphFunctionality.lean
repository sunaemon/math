module

public import PolishSpaceBook.FirstOrderOperationFunctionality

@[expose] public section

/-!
# Recursive graph values are provably functional

Open two disjoint blocks of child values. The induction hypothesis identifies
the corresponding children; equality transport aligns the operation inputs,
and operation functionality identifies the outputs.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- The unquantified application matrix only uses names below the end of its child block. -/
theorem fv_termGraph_matrix_bound {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ) (x B : ℕ) (hx : x < B)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) :
    ∀ a ∈ (binary .conj (conjoin n (fun i => D.termGraph (ts i) (B+i.val) (B+n)))
      (D.operationGraph f (fun i => .var (B+i.val)) x)).fv, a < B+n := by
  intro a ha
  rw [fv_binary] at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rw [fv_conjoin] at ha
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
    rcases Finset.mem_insert.mp (D.fv_termGraph_subset (ts i) _ _ hi) with he | hi
    · have := i.isLt; omega
    · have := ht i a hi; omega
  · rcases Finset.mem_insert.mp (D.fv_operationGraph_subset f _ x ha) with he | ha
    · omega
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
      have he : a = B+i.val := by simpa using hi
      have := i.isLt; omega

/-- The old theory proves equality of any two outputs of one recursive term graph. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Prove pairwise equality by induction on the term. The variable case follows by symmetry and transitivity.
    For an application with $n$ arguments, set $C=B+n$. In the second graph change the starting index from $B$ to
    $C$, using the independence of fresh starting indices proved above. Open the two child blocks with names
    $u_i=v_{B+i}$ and $w_i=v_{C+i}$. The blocks are disjoint. Each original parameter and both final outputs have
    indices below $B$.

    For each child, move the first graph's internal starting index from $B+n$ to $C+n$ by the same independence
    lemma. The induction hypothesis now gives $u_i=w_i$. Equality in simultaneous instances transports the first
    operation graph from the inputs $\vec{u}$ to $\vec{w}$, preserving its output. The second operation graph
    already has the latter inputs. Operation uniqueness therefore identifies the two final outputs. Discharge the
    second child block and then the first by existential elimination. The second block's names are not free in
    the first unquantified matrix, whose free names have indices below $C$. The first block's names are not free in
    the entire second graph. Neither block has a free occurrence in the final equality or the sentence assumptions.
    Thus these eliminations satisfy their eigenvariable conditions.
-/
theorem proves_termGraph_functional {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hx : x < B) (hy : y < B) (hxt : x ∉ t.varFinset) (hyt : y ∉ t.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) :
    ProvesFrom T (binary .imp (binary .conj (D.termGraph t x B) (D.termGraph t y B))
      (equal (.var x) (.var y))) := by
  induction t generalizing x y B with
  | var a =>
    refine ⟨∅, by simp, Derives.impIntro ?_⟩
    exact Derives.eq_trans (.andLeft (.hyp ∅ _)) (Derives.eq_symm (.andRight (.hyp ∅ _)))
  | @func n f ts ih =>
    let C := B+n
    let K := C+n
    let M (b w : ℕ) := binary .conj (conjoin n (fun i => D.termGraph (ts i) (b+i.val) (b+n)))
      (D.operationGraph f (fun i : Fin n => .var (b+i.val)) w)
    let A := binary .conj (D.termGraph (.func f ts) x B) (D.termGraph (.func f ts) y B)
    let χ : AlphaFormula L := equal (.var x) (.var y)
    let P (i : Fin n) := binary .imp
      (binary .conj (D.termGraph (ts i) (B+i.val) C) (D.termGraph (ts i) (C+i.val) K))
      (equal (.var (B+i.val)) (.var (C+i.val)))
    have hti (i : Fin n) (a : ℕ) (ha : a ∈ (ts i).varFinset) : a < B :=
      ht a (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)
    have hP (i : Fin n) : ProvesFrom T (P i) := by
      have hi := ih i (B+i.val) (C+i.val) K (by dsimp [K,C]; have := i.isLt; omega)
        (by dsimp [K,C]; have := i.isLt; omega)
        (fun hm => by have := hti i _ hm; omega)
        (fun hm => by have := hti i _ hm; dsimp only [C] at this; omega)
        (fun a ha => by have := hti i a ha; dsimp [K,C]; omega)
      have he := D.termGraph_bound_independent (ts i) (B+i.val) C K
        (by dsimp [C]; have := i.isLt; omega) (by dsimp [K,C]; have := i.isLt; omega)
        (fun a ha => by have := hti i a ha; dsimp [C]; omega)
        (fun a ha => by have := hti i a ha; dsimp [K,C]; omega)
      simpa only [P, he] using hi
    have hPs := ProvesFrom.conjoin n P hP
    have hop := D.proves_operationGraph_functional hT hu f (fun i : Fin n => C+i.val)
      (fun i j he => Fin.ext (by change C+i.val = C+j.val at he; omega)) x y
    apply ProvesFrom.map₂_sentences hT hPs hop
    intro Γ hΓ hPs hop
    have hA (a : ℕ) (ha : a ∈ A.fv) : a < B := by
      rw [fv_binary] at ha
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_insert.mp (D.fv_termGraph_subset (.func f ts) x B ha) with he | ha
        · omega
        · exact ht a ha
      · rcases Finset.mem_insert.mp (D.fv_termGraph_subset (.func f ts) y B ha) with he | ha
        · omega
        · exact ht a ha
    have hχ (a : ℕ) (ha : a ∈ χ.fv) : a < B := by
      change a ∈ ({x} ∪ {y} : Finset ℕ) at ha
      simp only [Finset.mem_union, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    have hM := D.fv_termGraph_matrix_bound f ts x B hx hti
    let Γ₁ := insert A Γ
    let Γ₂ := insert (M B x) Γ₁
    let Γ₃ := insert (M C y) Γ₂
    have hw : Γ ⊆ Γ₃ := by
      intro φ hφ
      simp [Γ₃, Γ₂, Γ₁, hφ]
    have hbody : Derives Γ₃ χ := by
      have hleft : Derives Γ₃ (M B x) := .assumption (by simp [Γ₃,Γ₂])
      have hright : Derives Γ₃ (M C y) := .hyp Γ₂ _
      have heq (i : Fin n) : Derives Γ₃ (equal (.var (B+i.val)) (.var (C+i.val))) := by
        apply Derives.impElim ((Derives.conjoin_elim n P hPs i).weaken hw)
        exact .andIntro (Derives.conjoin_elim n _ (.andLeft hleft) i)
          (Derives.conjoin_elim n _ (.andLeft hright) i)
      have ho := D.derives_operationGraph_congr f (fun i : Fin n => .var (B+i.val))
        (fun i => .var (C+i.val)) x x heq (.eqIntro Γ₃ (.var x)) (.andRight hleft)
      exact .impElim (hop.weaken hw) (.andIntro ho (.andRight hright))
    have hsecond : Derives Γ₂ (existsBlock n C (M C y)) := by
      have hh : Derives Γ₂ (D.termGraph (.func f ts) y B) :=
        .andRight (Derives.assumption (φ := A) (by simp [Γ₂,Γ₁]))
      have he := D.termGraph_bound_independent (.func f ts) y B C hy (by dsimp [C]; omega)
        ht (fun a ha => by have := ht a ha; dsimp [C]; omega)
      rw [he] at hh
      exact hh
    have hmiddle : Derives Γ₂ χ := by
      refine Derives.existsBlock_elim_self n C (M C y) χ ?_ ?_ hsecond hbody
      · intro i hm
        simp only [Γ₂,Γ₁,Context.fv_insert,hΓ,Finset.union_empty,Finset.mem_union] at hm
        rcases hm with hm | hm
        · have := hM _ hm; dsimp only [C] at this; omega
        · have := hA _ hm; dsimp only [C] at this; omega
      · intro i hm
        have := hχ _ hm; dsimp only [C] at this; omega
    apply Derives.impIntro
    refine Derives.existsBlock_elim_self n B (M B x) χ ?_ ?_ (.andLeft (.hyp Γ A)) hmiddle
    · intro i hm
      have hm' : B+i.val ∈ A.fv := by simpa only [Γ₁,Context.fv_insert,hΓ,Finset.union_empty] using hm
      have := hA _ hm'; omega
    · intro i hm
      have := hχ _ hm; omega

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
