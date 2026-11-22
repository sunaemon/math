module

public import PolishSpaceBook.FirstOrderAtomicConditionalSubstitution

@[expose] public section

/-!
# Relational substitution for function elimination

First keep the replacement graph as an assumption and induct on a representative
whose bound names avoid the substitution variables and the replacement term.
Bind the replacement value only after the conditional equivalence is proved.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance functionSubstitutionDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Substitution agrees under the replacement-value assumption on a fresh representative. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Choose a representative of the formula whose bound names avoid $x,y$ and every variable of $r$,
    using \termuseas{fresh bound names lemma}{lemma on fresh bound names}.
    Keep $\rho:=\FirstOrderTermGraph{r}{y}{B}$ as an assumption and prove
    $$T\vdash\rho\to\bigl(\chi\leftrightarrow\psi\subst{x}{y}\bigr)$$
    by structural induction, before binding the replacement value. The conditional implications in the proof of
    \termuse{relational substitution in atoms} give the atomic cases. At an atom, enlarge its witness starting index
    if needed to exceed its argument variables. Bound-name invariance identifies the replacement graph at this
    larger index with the original one, so the same assumption is retained throughout the induction.
-/
theorem proves_erase_subst_conditional_fresh {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (φ : Formula (L.sum (functionSymbols ι))) (r : (L.sum (functionSymbols ι)).Term ℕ)
    (x y B : ℕ) (hy : y < B) (hyr : y ∉ r.varFinset) (hr : ∀ a ∈ r.varFinset, a < B)
    (hb : Disjoint φ.boundNames (insert x (insert y r.varFinset))) :
    ProvesFrom T (binary .imp (D.termGraph r y B)
      (biimp (D.eraseFormula (φ.subst x r)) (D.eraseFormula (φ.subst x (.var y))))) := by
  induction φ with
  | falsum =>
    refine ⟨∅,by simp,Derives.impIntro ?_⟩
    exact .andIntro (.impIntro (.hyp _ falsum)) (.impIntro (.hyp _ falsum))
  | equal t u =>
    let C := B + valueBound ![t,u]
    have ht (a : ℕ) (ha : a ∈ t.varFinset) : a < C := by
      have := valueBound_spec ![t,u] 0 a ha; dsimp [C]; omega
    have ht' (a : ℕ) (ha : a ∈ u.varFinset) : a < C := by
      have := valueBound_spec ![t,u] 1 a ha; dsimp [C]; omega
    have hr' (a : ℕ) (ha : a ∈ r.varFinset) : a < C := by have := hr a ha; dsimp [C]; omega
    have hy' : y < C := by dsimp [C]; omega
    have hh := D.proves_eliminate_equal_conditional hT hu t u r x y C hy' hyr ht ht' hr'
    have he := D.termGraph_bound_independent r y B C hy hy' hr hr'
    simpa only [he,equal,subst_mk,eliminate_mk] using hh
  | rel R ts =>
    rcases R with R | R
    · let C := B + valueBound ts
      have ht (i) (a : ℕ) (ha : a ∈ (ts i).varFinset) : a < C := by
        have := valueBound_spec ts i a ha; dsimp [C]; omega
      have hr' (a : ℕ) (ha : a ∈ r.varFinset) : a < C := by have := hr a ha; dsimp [C]; omega
      have hy' : y < C := by dsimp [C]; omega
      have hh := D.proves_eliminate_rel_conditional hT hu R ts r x y C hy' hyr ht hr'
      have he := D.termGraph_bound_independent r y B C hy hy' hr hr'
      simpa only [he,rel,subst_mk,eliminate_mk] using hh
    · exact nomatch R
  | binary c φ ψ ihφ ihψ =>
    have hd := Finset.disjoint_union_left.mp hb
    simpa only [Formula.subst_binary,eraseFormula] using
      ProvesFrom.conditional_binary hT (D.termGraph r y B) c (ihφ hd.1) (ihψ hd.2)
  | quant q z φ ih =>
    have hd : z ∉ insert x (insert y r.varFinset) ∧
        Disjoint φ.boundNames (insert x (insert y r.varFinset)) := Finset.disjoint_insert_left.mp hb
    have hz : z ≠ x ∧ z ≠ y ∧ z ∉ r.varFinset := by simpa using hd.1
    have hzy : z ∉ (Term.var y : (L.sum (functionSymbols ι)).Term ℕ).varFinset := by
      simpa only [Term.varFinset,Finset.mem_singleton] using hz.2.1
    have hρ : z ∉ (D.termGraph r y B).fv := by
      intro hm
      rcases Finset.mem_insert.mp (D.fv_termGraph_subset r y B hm) with he | hm
      · exact hz.2.1 he
      · exact hz.2.2 hm
    simpa only [Formula.subst_quant,ite_eq_right hz.1,ite_eq_left hz.2.2,ite_eq_left hzy,eraseFormula] using
      ProvesFrom.conditional_quant hT (D.termGraph r y B) q z hρ (ih hd.2)

/-- Conditional relational substitution is independent of representatives and bound-name choices. -/
theorem proves_eliminate_subst_conditional {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (φ : AlphaFormula (L.sum (functionSymbols ι))) (r : (L.sum (functionSymbols ι)).Term ℕ)
    (x y B : ℕ) (hy : y < B) (hyr : y ∉ r.varFinset) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .imp (D.termGraph r y B)
      (biimp (D.eliminate (φ.subst x r)) ((D.eliminate φ).subst x (.var y)))) := by
  rw [← D.eliminate_subst_var]
  obtain ⟨ψ,he,hψ⟩ := φ.exists_fresh_rep (insert x (insert y r.varFinset))
  rw [← he,subst_mk,subst_mk,eliminate_mk,eliminate_mk]
  exact D.proves_erase_subst_conditional_fresh hT hu ψ r x y B hy hyr hr hψ

/-- Arbitrary term substitution is expressed by existentially binding its recursive graph value. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Relational substitution
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Finally, the existence lemma supplies the replacement value. The variable $y$ is not free in $\chi$, by the
    free-variable formulas for substitution and translation. Apply the shared value-binding argument from
    \termuse{relational substitution in atoms} to obtain the displayed equivalence.
-/
theorem proves_eliminate_substitution {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (φ : AlphaFormula (L.sum (functionSymbols ι))) (r : (L.sum (functionSymbols ι)).Term ℕ)
    (x y B : ℕ) (hy : y < B) (hyr : y ∉ r.varFinset) (hyφ : y ∉ φ.fv)
    (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (biimp (D.eliminate (φ.subst x r))
      (quant .ex y (binary .conj (D.termGraph r y B) ((D.eliminate φ).subst x (.var y))))) := by
  have hys : y ∉ (φ.subst x r).fv := by
    rw [fv_subst]
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hyφ (Finset.mem_erase.mp hm).2
    · split_ifs at hm
      · exact hyr hm
      · exact Finset.notMem_empty y hm
  have hyχ : y ∉ (D.eliminate (φ.subst x r)).fv := fun hm => hys (D.fv_eliminate_subset _ hm)
  exact ProvesFrom.bind_conditional_biimp hT (D.termGraph r y B) (D.eliminate (φ.subst x r))
    ((D.eliminate φ).subst x (.var y)) y hyχ (D.proves_termGraph_exists hT hu r y B hy hyr hr)
    (D.proves_eliminate_subst_conditional hT hu φ r x y B hy hyr hr)

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
