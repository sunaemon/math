module

public import PolishSpaceBook.FirstOrderFunctionVariableSubstitution

@[expose] public section

/-!
# Substitution of arbitrary terms in recursive graphs

A value of the replacement term can be used in place of that term throughout
another term graph. The forward direction is a direct induction on the outer
term, retaining the original operation graph at each application. For the
converse, obtain an outer value and use functionality of the substituted graph.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance termGraphSubstitutionDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _

/-- Bounds on both terms bound every variable after substitution. -/
theorem termSubst_vars_below (t r : L.Term ℕ) (x B : ℕ)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    ∀ a ∈ (termSubst t x r).varFinset, a < B := by
  intro a ha
  rcases (mem_varFinset_termSubst t x r a).mp ha with ha | ha
  · exact ht a ha.1
  · exact hr a ha.2

namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- A graph at a fresh output can be transported along a proved equality of values. -/
theorem derives_termGraph_output {Γ : Context L}
    (t : (L.sum (functionSymbols ι)).Term ℕ) (y w B : ℕ)
    (hy : y < B) (hw : w < B) (hyt : y ∉ t.varFinset)
    (h : Derives Γ (D.termGraph t y B)) (he : Derives Γ (equal (.var y) (.var w))) :
    Derives Γ (D.termGraph t w B) := by
  have hd := Derives.eqElim (D.termGraph t y B) y (.var y) (.var w)
    (by simpa only [subst_self] using h) he
  simpa only [D.termGraph_subst_output t y w B hy hw hyt] using hd

/-- Substitution of a term value into an outer graph yields the graph of the substituted term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    First assume the graph of the replacement value and the outer graph with that value substituted.
    Induct on the outer term to derive the graph with the term itself substituted. At the variable being replaced,
    the outer graph equates its output with the replacement value; equality elimination transports the replacement
    graph to that output. At any other variable, the value equation is unchanged. At an application with $n$
    arguments, open the child values $v_{B+i}$ for $i<n$. Move the replacement graph's internal starting index to
    $B+n$, using bound-name invariance, and apply induction to each child. The operation graph is unchanged.
    Conjoin the resulting child graphs with it and introduce their existential block. Discharge the original child
    block by existential elimination: its names are not free in the original assumptions or final graph, whose
    free-variable indices are below $B$. This also covers the empty child block of a constant.
-/
theorem derives_termGraph_substitution {Γ : Context L}
    (t r : (L.sum (functionSymbols ι)).Term ℕ) (x y w B : ℕ)
    (hΓ : ∀ a ∈ Γ.fv, a < B) (hy : y < B) (hw : w < B)
    (hyr : y ∉ r.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ a ∈ r.varFinset, a < B)
    (hv : Derives Γ (D.termGraph r y B))
    (hg : Derives Γ (D.termGraph (termSubst t x (.var y)) w B)) :
    Derives Γ (D.termGraph (termSubst t x r) w B) := by
  induction t generalizing Γ w B with
  | var a =>
    by_cases ha : a = x
    · subst a
      simp only [termSubst_var_self, termGraph] at hg ⊢
      exact D.derives_termGraph_output r y w B hy hw hyr hv (Derives.eq_symm hg)
    · simpa only [termSubst, Term.subst, ite_eq_right ha] using hg
  | @func n f ts ih =>
    let us : Fin n → (L.sum (functionSymbols ι)).Term ℕ := fun i => termSubst (ts i) x (.var y)
    let vs : Fin n → (L.sum (functionSymbols ι)).Term ℕ := fun i => termSubst (ts i) x r
    let M := binary .conj (conjoin n (fun i => D.termGraph (us i) (B+i.val) (B+n)))
      (D.operationGraph f (fun i : Fin n => .var (B+i.val)) w)
    let N := binary .conj (conjoin n (fun i => D.termGraph (vs i) (B+i.val) (B+n)))
      (D.operationGraph f (fun i : Fin n => .var (B+i.val)) w)
    let χ := D.termGraph (.func f vs) w B
    have hti (i : Fin n) (a : ℕ) (ha : a ∈ (ts i).varFinset) : a < B :=
      ht a (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)
    have hui (i : Fin n) : ∀ a ∈ (us i).varFinset, a < B :=
      termSubst_vars_below (ts i) (.var y) x B (hti i) (by simpa using hy)
    have hvi (i : Fin n) : ∀ a ∈ (vs i).varFinset, a < B :=
      termSubst_vars_below (ts i) r x B (hti i) hr
    have hM := D.fv_termGraph_matrix_bound f us w B hw hui
    have hχ (a : ℕ) (ha : a ∈ χ.fv) : a < B := by
      rcases Finset.mem_insert.mp (D.fv_termGraph_subset (.func f vs) w B ha) with he | ha
      · simpa only [he] using hw
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
        exact hvi i a hi
    have hb : Derives (insert M Γ) χ := by
      have hv' : Derives (insert M Γ) (D.termGraph r y (B+n)) := by
        have he := D.termGraph_bound_independent r y B (B+n) hy (by omega)
          hr (fun a ha => by have := hr a ha; omega)
        rw [← he]
        exact hv.weaken (Finset.subset_insert _ _)
      have hc (i : Fin n) : Derives (insert M Γ) (D.termGraph (vs i) (B+i.val) (B+n)) := by
        apply ih i (Γ := insert M Γ) (B+i.val) (B+n)
        · intro a ha
          rw [Context.fv_insert, Finset.mem_union] at ha
          exact ha.elim (hM a) (fun ha => by have := hΓ a ha; omega)
        · omega
        · have := i.isLt; omega
        · intro a ha; have := hti i a ha; omega
        · intro a ha; have := hr a ha; omega
        · exact hv'
        · exact Derives.conjoin_elim n _ (.andLeft (.hyp Γ M)) i
      exact Derives.existsBlock_intro_self n B N
        (.andIntro (Derives.conjoin_intro n _ hc) (.andRight (.hyp Γ M)))
    exact Derives.existsBlock_elim_self n B M χ
      (fun i hm => by have := hΓ _ hm; omega)
      (fun i hm => by have := hχ _ hm; omega) hg hb

/-- Any bound on the parameters and output bounds the free variables of a graph. -/
theorem termGraph_fv_below (t : (L.sum (functionSymbols ι)).Term ℕ) (w K B : ℕ)
    (hw : w < B) (ht : ∀ a ∈ t.varFinset, a < B) :
    ∀ a ∈ (D.termGraph t w K).fv, a < B := by
  intro a ha
  rcases Finset.mem_insert.mp (D.fv_termGraph_subset t w K ha) with he | ha
  · simpa only [he] using hw
  · exact ht a ha

/-- The forward substitution implication needs no nonlogical assumptions. -/
theorem proves_termGraph_substitution {T : Set (AlphaFormula L)}
    (t r : (L.sum (functionSymbols ι)).Term ℕ) (x y w B : ℕ)
    (hy : y < B) (hw : w < B) (hyr : y ∉ r.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .imp
      (binary .conj (D.termGraph r y B) (D.termGraph (termSubst t x (.var y)) w B))
      (D.termGraph (termSubst t x r) w B)) := by
  refine ⟨∅,by simp,Derives.impIntro ?_⟩
  apply D.derives_termGraph_substitution t r x y w B _ hy hw hyr ht hr
    (.andLeft (.hyp ∅ _)) (.andRight (.hyp ∅ _))
  intro a ha
  have he : (∅ : Context L).fv = ∅ := Finset.biUnion_empty
  simp only [Context.fv_insert,he,Finset.union_empty,fv_binary,Finset.mem_union] at ha
  exact ha.elim (D.termGraph_fv_below r y B B hy hr a)
    (D.termGraph_fv_below _ w B B hw (termSubst_vars_below t (.var y) x B ht (by simpa using hy)) a)

/-- Existence and uniqueness recover the outer graph from a graph of the substituted term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the converse under the replacement-value assumption, take a value $u=v_B$ of the outer term
    $t\subst{x}{y}$, using existence with internal starting index $C=B+1$. The preceding direction gives the graph
    of $t\subst{x}{r}$ at $u$. Change the given graph at $w$ to the same internal starting index.
    Uniqueness identifies these two values. Equality elimination in the outer graph then replaces its output
    $u$ by $w$, and bound-name invariance restores its starting index to $B$.
    The auxiliary name is absent from the parameters and conclusion, so existential elimination discharges its
    temporary graph assumption. This proves the converse without a second induction on terms.
-/
theorem proves_termGraph_substitution_reverse {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t r : (L.sum (functionSymbols ι)).Term ℕ) (x y w B : ℕ)
    (hy : y < B) (hw : w < B) (hyr : y ∉ r.varFinset)
    (hwt : w ∉ t.varFinset) (hwr : w ∉ r.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .imp
      (binary .conj (D.termGraph r y B) (D.termGraph (termSubst t x r) w B))
      (D.termGraph (termSubst t x (.var y)) w B)) := by
  let s := termSubst t x (.var y)
  let q := termSubst t x r
  let C := B+1
  let A := binary .conj (D.termGraph r y B) (D.termGraph q w B)
  let ρ := D.termGraph s B C
  let χ := D.termGraph s w B
  have hs : ∀ a ∈ s.varFinset, a < B := termSubst_vars_below t (.var y) x B ht (by simpa using hy)
  have hq : ∀ a ∈ q.varFinset, a < B := termSubst_vars_below t r x B ht hr
  have hB (v : (L.sum (functionSymbols ι)).Term ℕ) (hv : ∀ a ∈ v.varFinset, a < B) :
      B ∉ v.varFinset := fun hm => by have := hv B hm; omega
  have hwq : w ∉ q.varFinset := by
    intro hm
    rcases (mem_varFinset_termSubst t x r w).mp hm with hm | hm
    · exact hwt hm.1
    · exact hwr hm.2
  have hex := D.proves_termGraph_exists hT hu s B C (by dsimp [C]; omega)
    (hB s hs) (fun a ha => by have := hs a ha; dsimp [C]; omega)
  have hfun := D.proves_termGraph_functional hT hu q B w C (by dsimp [C]; omega)
    (by dsimp [C]; omega) (hB q hq) hwq (fun a ha => by have := hq a ha; dsimp [C]; omega)
  apply ProvesFrom.map₂_sentences hT hex hfun
  intro Γ hΓ hex hfun
  have hA (a : ℕ) (ha : a ∈ A.fv) : a < B := by
    rw [fv_binary] at ha
    exact (Finset.mem_union.mp ha).elim (D.termGraph_fv_below r y B B hy hr a)
      (D.termGraph_fv_below q w B B hw hq a)
  have hχ := D.termGraph_fv_below s w B B hw hs
  let Δ := insert A Γ
  let Θ := insert ρ Δ
  have hΘ (a : ℕ) (ha : a ∈ Θ.fv) : a < C := by
    simp only [Θ,Δ,Context.fv_insert,hΓ,Finset.union_empty,Finset.mem_union] at ha
    exact ha.elim (D.termGraph_fv_below s B C C (by dsimp [C]; omega)
      (fun a ha => by have := hs a ha; dsimp [C]; omega) a)
      (fun ha => by have := hA a ha; dsimp [C]; omega)
  have hwΓ : Γ ⊆ Θ := by intro φ hφ; simp [Θ,Δ,hφ]
  have hbody : Derives Θ χ := by
    have hA' : Derives Θ A := .assumption (by simp [Θ,Δ])
    have hv : Derives Θ (D.termGraph r y C) := by
      rw [← D.termGraph_bound_independent r y B C hy (by dsimp [C]; omega)
        hr (fun a ha => by have := hr a ha; dsimp [C]; omega)]
      exact .andLeft hA'
    have hqB := D.derives_termGraph_substitution t r x y B C hΘ
      (by dsimp [C]; omega) (by dsimp [C]; omega) hyr
      (fun a ha => by have := ht a ha; dsimp [C]; omega)
      (fun a ha => by have := hr a ha; dsimp [C]; omega) hv (.hyp Δ ρ)
    have hqw : Derives Θ (D.termGraph q w C) := by
      rw [← D.termGraph_bound_independent q w B C hw (by dsimp [C]; omega)
        hq (fun a ha => by have := hq a ha; dsimp [C]; omega)]
      exact .andRight hA'
    have he := Derives.impElim (hfun.weaken hwΓ) (.andIntro hqB hqw)
    have hout := D.derives_termGraph_output s B w C (by dsimp [C]; omega)
      (by dsimp [C]; omega) (hB s hs) (Derives.hyp Δ ρ) he
    have hb := D.termGraph_bound_independent s w B C hw (by dsimp [C]; omega)
      hs (fun a ha => by have := hs a ha; dsimp [C]; omega)
    simpa only [χ,hb] using hout
  apply Derives.impIntro
  refine Derives.exElim B B ρ χ (hex.weaken (Finset.subset_insert _ _))
    (by simpa only [subst_self] using hbody) ?_
  have hBΔ : B ∉ Δ.fv := by
    intro hm
    have hm' : B ∈ A.fv := by simpa only [Δ,Context.fv_insert,hΓ,Finset.union_empty] using hm
    have := hA B hm'; omega
  have hBχ : B ∉ χ.fv := fun hm => by have := hχ B hm; omega
  simp only [Finset.mem_union,fv_quant,Finset.mem_erase,ne_eq,not_true_eq_false,
    false_and,or_false,not_or]
  exact ⟨hBΔ,hBχ⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
