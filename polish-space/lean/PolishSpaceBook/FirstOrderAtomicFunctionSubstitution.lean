module

public import PolishSpaceBook.FirstOrderArgumentGraphTransfer
public import PolishSpaceBook.FirstOrderProofCongruence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Relational substitution in atomic function elimination

One shared value of the replacement term serves every argument of an atom.
The continuation may be any formula using only the argument value slots.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance atomicFunctionSubstitutionDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Keep the replacement value fixed while comparing the two atomic continuations. -/
theorem proves_withValues_substitution_conditional {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ}
    (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (r : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ) (ψ : AlphaFormula L)
    (hy : y < B) (hyr : y ∉ r.varFinset)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) (hr : ∀ a ∈ r.varFinset, a < B)
    (hψ : ψ.fv ⊆ temporaryNames n B) :
    ProvesFrom T (binary .imp (D.termGraph r y B)
      (biimp (D.withValues (fun i => termSubst (ts i) x r) B ψ)
        (D.withValues (fun i => termSubst (ts i) x (.var y)) B ψ))) := by
  let vs := fun i => termSubst (ts i) x (.var y)
  let us := fun i => termSubst (ts i) x r
  let ρ := D.termGraph r y B
  have hv (i : Fin n) : ∀ a ∈ (vs i).varFinset, a < B :=
    termSubst_vars_below (ts i) (.var y) x B (ht i) (by simpa using hy)
  have hu' (i : Fin n) : ∀ a ∈ (us i).varFinset, a < B := termSubst_vars_below (ts i) r x B (ht i) hr
  have hρ := D.termGraph_fv_below r y B B hy hr
  have he := D.termGraph_bound_independent r y B (B+n) hy (by omega)
    hr (fun a ha => by have := hr a ha; omega)
  have hf (i : Fin n) : ProvesFrom T (binary .imp
      (binary .conj ρ (D.termGraph (vs i) (B+i.val) (B+n)))
      (D.termGraph (us i) (B+i.val) (B+n))) := by
    have h := D.proves_termGraph_substitution (T := T) (ts i) r x y (B+i.val) (B+n)
      (by omega) (by have := i.isLt; omega) hyr
      (fun a ha => by have := ht i a ha; omega) (fun a ha => by have := hr a ha; omega)
    simpa only [ρ,he] using h
  have hb (i : Fin n) : ProvesFrom T (binary .imp
      (binary .conj ρ (D.termGraph (us i) (B+i.val) (B+n)))
      (D.termGraph (vs i) (B+i.val) (B+n))) := by
    have h := D.proves_termGraph_substitution_reverse hT hu (ts i) r x y (B+i.val) (B+n)
      (by omega) (by have := i.isLt; omega) hyr
      (fun hm => by have := ht i _ hm; omega) (fun hm => by have := hr _ hm; omega)
      (fun a ha => by have := ht i a ha; omega) (fun a ha => by have := hr a ha; omega)
    simpa only [ρ,he] using h
  have hforward := D.proves_withValues_map hT vs us B ρ ψ hρ hψ hv hu' hf
  have hbackward := D.proves_withValues_map hT us vs B ρ ψ hρ hψ hu' hv hb
  exact ProvesFrom.conditional_biimp hT ρ (D.withValues us B ψ) (D.withValues vs B ψ)
    hbackward hforward

/-- Bind one replacement value shared by all arguments, including an empty argument family. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Assume the graph of the replacement value. For each of the $n$ arguments, the two conditional implications
    in the term-graph substitution proof transform its graph in either direction. The child output is $v_{B+i}$,
    its internal starting index is $B+n$, and this output is absent from the original arguments and replacement
    term. Move the replacement graph to this internal starting index by bound-name invariance.
    Open the block of argument values, apply the appropriate implication to each child, retain the final relation
    or equality, and reintroduce the same block. The original assumptions and the final translated atom contain no
    free witness name, so existential elimination discharges the opened block. This is one argument for any finite
    number of argument positions, including zero; equality uses two positions.
-/
theorem proves_withValues_substitution {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ}
    (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (r : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ) (ψ : AlphaFormula L)
    (hy : y < B) (hyr : y ∉ r.varFinset) (hyt : ∀ i, y ∉ (ts i).varFinset)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) (hr : ∀ a ∈ r.varFinset, a < B)
    (hψ : ψ.fv ⊆ temporaryNames n B) :
    ProvesFrom T (binary .conj
      (binary .imp (D.withValues (fun i => termSubst (ts i) x r) B ψ)
        (quant .ex y (binary .conj (D.termGraph r y B)
          (D.withValues (fun i => termSubst (ts i) x (.var y)) B ψ))))
      (binary .imp (quant .ex y (binary .conj (D.termGraph r y B)
          (D.withValues (fun i => termSubst (ts i) x (.var y)) B ψ)))
        (D.withValues (fun i => termSubst (ts i) x r) B ψ))) := by
  let vs := fun i => termSubst (ts i) x (.var y)
  let us := fun i => termSubst (ts i) x r
  let ρ := D.termGraph r y B
  have hyχ : y ∉ (D.withValues us B ψ).fv := by
    intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (D.fv_withValues_atom us B ψ hψ hm)
    rcases (mem_varFinset_termSubst (ts i) x r y).mp hi with hi | hi
    · exact hyt i hi.1
    · exact hyr hi.2
  exact ProvesFrom.bind_conditional_biimp hT ρ (D.withValues us B ψ) (D.withValues vs B ψ) y hyχ
    (D.proves_termGraph_exists hT hu r y B hy hyr hr)
    (D.proves_withValues_substitution_conditional hT hu ts r x y B ψ hy hyr ht hr hψ)

/-- An atomic relation can use any admissible starting index for its witnesses. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For a relation or equality, use the common starting index $B$ for the argument witnesses in both translations.
    This is admissible after either substitution. Pairing the corresponding witness positions, as in the proof of
    bound-name invariance, identifies these formulas up to $\alpha$-equivalence with the translations using their
    originally chosen indices. Translation also commutes with variable substitution by the earlier lemma.
-/
theorem eliminate_rel_at {n : ℕ} (R : L.Relations n)
    (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ) (B : ℕ)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) :
    D.eliminate (rel (Sum.inl R) ts) = D.withValues ts B (relationValues R B) := by
  change D.withValues ts (valueBound ts) (relationValues R (valueBound ts)) = _
  apply Corresponds.eq
  apply D.withValues_corresponds ts ts Eq _ _ _ _ (fun i => TermRel.refl (ts i)) (valueBound_spec ts) ht
  exact Corresponds.rel R (fun i => .var (bindBlock_position Eq n _ _ i))

/-- An equality can use any admissible starting index for its two witnesses. -/
theorem eliminate_equal_at (t r : (L.sum (functionSymbols ι)).Term ℕ) (B : ℕ)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    D.eliminate (equal t r) = D.withValues ![t,r] B (equalValues B) := by
  change D.withValues ![t,r] (valueBound ![t,r]) (equalValues (valueBound ![t,r])) = _
  apply Corresponds.eq
  refine D.withValues_corresponds ![t,r] ![t,r] Eq _ _ _ _ (fun i => TermRel.refl _) (valueBound_spec _) ?_ ?_
  · intro i; fin_cases i
    · exact ht
    · exact hr
  · exact Corresponds.equal (.var (bindBlock_position Eq 2 _ _ 0)) (.var (bindBlock_position Eq 2 _ _ 1))

/-- Relational substitution for the canonical translation of an atomic relation. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Relational substitution in atoms
-/
theorem proves_eliminate_rel_substitution {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ} (R : L.Relations n)
    (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (r : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hy : y < B) (hyr : y ∉ r.varFinset) (hyt : ∀ i, y ∉ (ts i).varFinset)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .conj
      (binary .imp (D.eliminate ((rel (Sum.inl R) ts).subst x r))
        (quant .ex y (binary .conj (D.termGraph r y B)
          ((D.eliminate (rel (Sum.inl R) ts)).subst x (.var y)))))
      (binary .imp (quant .ex y (binary .conj (D.termGraph r y B)
          ((D.eliminate (rel (Sum.inl R) ts)).subst x (.var y))))
        (D.eliminate ((rel (Sum.inl R) ts).subst x r)))) := by
  rw [← D.eliminate_subst_var,subst_rel,subst_rel]
  rw [D.eliminate_rel_at R _ B (fun i => termSubst_vars_below (ts i) r x B (ht i) hr),
    D.eliminate_rel_at R _ B
      (fun i => termSubst_vars_below (ts i) (.var y) x B (ht i) (by simpa using hy))]
  exact D.proves_withValues_substitution hT hu ts r x y B (relationValues R B)
    hy hyr hyt ht hr (fv_relationValues_subset R B)

/-- Relational substitution for the canonical translation of an atomic equality. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Relational substitution in atoms
-/
theorem proves_eliminate_equal_substitution {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t u r : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hy : y < B) (hyr : y ∉ r.varFinset) (hyt : y ∉ t.varFinset) (hyu : y ∉ u.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) (hu' : ∀ a ∈ u.varFinset, a < B)
    (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .conj
      (binary .imp (D.eliminate ((equal t u).subst x r))
        (quant .ex y (binary .conj (D.termGraph r y B)
          ((D.eliminate (equal t u)).subst x (.var y)))))
      (binary .imp (quant .ex y (binary .conj (D.termGraph r y B)
          ((D.eliminate (equal t u)).subst x (.var y))))
        (D.eliminate ((equal t u).subst x r)))) := by
  rw [← D.eliminate_subst_var,subst_equal,subst_equal]
  rw [D.eliminate_equal_at _ _ B (termSubst_vars_below t r x B ht hr)
      (termSubst_vars_below u r x B hu' hr),
    D.eliminate_equal_at _ _ B (termSubst_vars_below t (.var y) x B ht (by simpa using hy))
      (termSubst_vars_below u (.var y) x B hu' (by simpa using hy))]
  have hv (a : (L.sum (functionSymbols ι)).Term ℕ) :
      (fun i : Fin 2 => termSubst (![t,u] i) x a) = ![termSubst t x a,termSubst u x a] := by
    funext i; fin_cases i <;> rfl
  have hh := D.proves_withValues_substitution hT hu ![t,u] r x y B (equalValues B) hy hyr
    (by intro i; fin_cases i; exact hyt; exact hyu)
    (by intro i; fin_cases i; exact ht; exact hu') hr (fv_equalValues_subset B)
  simpa only [hv] using hh

/-- Falsity is the remaining base case for relational substitution. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Relational substitution in atoms
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For falsity, each conditional implication simply extracts falsity from its conjunction with the value graph.
    The same value-binding argument applies, giving the remaining base case.
-/
theorem proves_falsum_value_binding {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (r : (L.sum (functionSymbols ι)).Term ℕ) (y B : ℕ)
    (hy : y < B) (hyr : y ∉ r.varFinset) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .conj
      (binary .imp falsum (quant .ex y (binary .conj (D.termGraph r y B) falsum)))
      (binary .imp (quant .ex y (binary .conj (D.termGraph r y B) falsum)) falsum)) := by
  have h : ProvesFrom T (binary .imp (binary .conj (D.termGraph r y B) falsum) falsum) :=
    ⟨∅,by simp,Derives.impIntro (.andRight (.hyp ∅ _))⟩
  exact ProvesFrom.bind_value_equivalence hT _ falsum falsum y (by simp [fv_falsum])
    (D.proves_termGraph_exists hT hu r y B hy hyr hr) h h

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
