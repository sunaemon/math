module

public import PolishSpaceBook.CantorInternalUnionInputs
public import PolishSpaceBook.CantorNodeAdmissibility

@[expose] public section

/-! # Internally chosen approximation families with external inclusion and error bounds -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression
universe u

/-- The induction hypothesis at the children gives one internal family of genuine external approximants. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internally selected child approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Absent children have empty interpretation, which belongs to $\mathcal R_M$ by the internal open-code
    construction applied to the empty code. Thus the approximation hypothesis holds for every child.
    Nodewise internal totality supplies witnesses for the errors $1/2^{k+2+n}$. The preceding input-graph
    proposition verifies the hypotheses of internal family selection, giving an internal graph of pairs
    $\langle W_n,V_n\rangle$ satisfying the admissibility formula at all children.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The nodewise admissibility theorem decodes these sets as $W_n=W_{T_n}$ and $V_n=W_{S_n}$ and proves the
    external inclusions and error bounds. These equalities preserve the entire paired graph, so decoding
    does not replace the internally selected family by an unrelated external choice. No computable
    selection of the approximations is asserted.
-/
theorem internally_selected_child_approximations {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (s : List ℕ) (k : ℕ)
    (hA : ∀ n, c (s ++ [n]) ≠ 0 → InternallyApproximable M (cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]))) :
    ∃ T S : ℕ → Set (List Bool),
      sequenceGraph (fun n => pair (wordTreeSet (binaryLift (T n))) (wordTreeSet (binaryLift (S n)))) ∈ M ∧
      ∀ n, wordTreeSet (binaryLift (T n)) ∈ M ∧ wordTreeSet (binaryLift (S n)) ∈ M ∧
        IsSubtree (T n) ∧ IsSubtree (S n) ∧
        (treeBody (T n) ⊆ cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]) ∧
          cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]) ⊆ (treeBody (S n))ᶜ) ∧
        fairCoinProduct.real (treeBody (T n) ∪ treeBody (S n))ᶜ < unionApproximationError k n := by
  have hAall (n : ℕ) : InternallyApproximable M (cantorNodeSet c hc.2.2.2.2.2 (s ++ [n])) := by
    by_cases hn : c (s ++ [n]) = 0
    · rw [cantorNodeSet_eq_empty c hc.2.2.2.2.2 _ hn]
      exact internallyApproximable_empty hM hinf hpair hunion hpower hsep
    · exact hA n hn
  have hF₂ := binaryWords_mem hM hinf hpair hunion hpower hsep
  let base : Fin 12 → M := fun i =>
    ⟨nodeApproximationValues M c hc.2.2.2.2.2 s (wordTreeSet (binaryLift Set.univ))
      (wordTreeSet (binaryLift Set.univ)) 1 1 i,
      nodeApproximationValues_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM s _ _ hF₂ hF₂ 1 1 i⟩
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) (base 0).property
  let B (n : ℕ) : M := ⟨internalInterpretation M c hc.2.2.2.2.2 NamedLambda.NatListCode.decode (s ++ [n]),
    canonical_internalInterpretation_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM _⟩
  let a (_ : ℕ) : M := base 10
  let d (n : ℕ) : M := ⟨natOrdinal (2 ^ (k + 2 + n)), hn _⟩
  let row (n : ℕ) (W V : M) : Fin 12 → M :=
    ![base 0, base 1, base 2, base 3, base 4, base 5, B n, base 7, W, V, a n, d n]
  have hrow (n : ℕ) (W V : M) : Subtype.val ∘ row n W V =
      nodeApproximationValues M c hc.2.2.2.2.2 (s ++ [n]) W.val V.val 1 (2 ^ (k + 2 + n)) := by
    funext i; fin_cases i <;> rfl
  have hb (n : ℕ) : 0 < (2 : ℕ) ^ (k + 2 + n) := pow_pos (by decide) _
  have htotal (n : ℕ) : ∃ W V : M, approximationAdmissibleFormula.Realize Empty.elim (row n W V) := by
    obtain ⟨T, S, hT, hS, q, hq, hφ⟩ := exists_admissible_at_node hM hinf hpair hunion hpower hsep hrep hchoice
      c hc hcM (s ++ [n]) (hAall n) 1 (2 ^ (k + 2 + n)) (by decide) (hb n) (hb n)
    let W : M := ⟨wordTreeSet (binaryLift T), hT⟩
    let V : M := ⟨wordTreeSet (binaryLift S), hS⟩
    refine ⟨W, V, ?_⟩
    have he : q = row n W V := by
      funext i
      apply Subtype.ext
      exact congrFun (hq.trans (hrow n W V).symm) i
    rwa [← he]
  obtain ⟨W, V, hgraph, hWV⟩ := internal_child_admissible_family hM hinf hpair hunion hpower hsep hrep hchoice
    c hc.2.2.2.2.2 NamedLambda.NatListCode.decode hcM
    (canonicalBasisWordGraph_mem hM hinf hpair hunion hpower hsep) s k
    (base 0) (base 1) (base 2) (base 3) (base 4) (base 5) (base 7) rfl
    B a d (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) htotal
  have hex (n : ℕ) := decode_node_admissible hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
    (s ++ [n]) (W n) (V n) 1 (2 ^ (k + 2 + n)) (hb n) (hb n)
    (row n (W n) (V n)) (hrow n (W n) (V n)) (hWV n)
  choose T S hT hS hprop using hex
  refine ⟨T, S, ?_, fun n => ⟨hT n ▸ (W n).property, hS n ▸ (V n).property, ?_⟩⟩
  · have he : (fun n => pair (wordTreeSet (binaryLift (T n))) (wordTreeSet (binaryLift (S n)))) =
        fun n => pair (W n).val (V n).val := by
      funext n
      rw [hT n, hS n]
    rwa [he]
  · simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, unionApproximationError] using hprop n

end PolishSpaceBook.CantorTreeMeasure
