module

public import PolishSpaceBook.BorelBoundedRows
public import PolishSpaceBook.BorelInclusionTree
public import PolishSpaceBook.SetTheoryWordMap
public import PolishSpaceBook.SetTheoryTreeRanks

@[expose] public section

/-! # Internal counterexample node sets from a single reflected predicate -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels NamedLambda
open BoundedSetPredicate
universe u

/-- Common numerical graphs, the original tree, and the candidate word. -/
def inclusionNodeParams (c : BorelExpression) (T : Set (List ℕ)) (w : List ℕ)
    (bit : Bool := false) : Fin 18 → ZFSet.{u} :=
  Fin.snoc (Fin.snoc (finiteRowParams c bit 0 [] []) (wordTreeSet T)) (wordGraph w)

def wordMapAt {n : ℕ} (Ω G s t : Fin n) : BoundedSetPredicate n :=
  wordMapPredicate.rename ![Ω, G, s, t]

lemma eval_wordMapAt {n : ℕ} (Ω G s t : Fin n) (xs : Fin n → ZFSet.{u}) :
    (wordMapAt Ω G s t).eval xs ↔ SetWordMap (xs Ω) (xs G) (xs s) (xs t) := by
  rw [wordMapAt, eval_rename]
  rfl

/-- Project a candidate word into the point and the certificate of the prescribed root bit. -/
def inclusionTestPredicate : BoundedSetPredicate 18 :=
  .ex 1 (.ex 1 (.conj (wordMapAt 0 7 17 18)
    (.conj (wordMapAt 0 8 17 19)
    (.conj (.member 18 16)
      (boundedRowsPredicate.rename ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 15])))))

lemma eval_inclusionTestPredicate (c : BorelExpression) (T : Set (List ℕ)) (w : List ℕ)
    (bit : Bool := false) :
    inclusionTestPredicate.eval (inclusionNodeParams.{u} c T w bit) ↔ inclusionTest c T w bit := by
  simp only [inclusionTestPredicate, eval, eval_wordMapAt, eval_rename]
  change (∃ x ∈ finiteSequences, ∃ q ∈ finiteSequences,
    SetWordMap Ordinal.omega0.toZFSet (sequenceGraph (fun n => natOrdinal n.unpair.1)) (wordGraph w) x ∧
    SetWordMap Ordinal.omega0.toZFSet (sequenceGraph (fun n => natOrdinal n.unpair.2)) (wordGraph w) q ∧
    x ∈ wordTreeSet T ∧ boundedRowsPredicate.eval
      ((Fin.snoc (Fin.snoc (inclusionNodeParams c T w bit) x) q) ∘
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 15])) ↔ _
  simp only [exists_mem_finiteSequences, setWordMap_iff, exists_and_left, exists_eq_left]
  have he : Fin.snoc (Fin.snoc (inclusionNodeParams.{u} c T w bit)
      (wordGraph (w.map (fun a => a.unpair.1)))) (wordGraph (w.map (fun a => a.unpair.2))) ∘
        ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 15] =
      finiteRowParams c bit 0 (w.map (fun a => a.unpair.1)) (w.map (fun a => a.unpair.2)) := by
    funext j; fin_cases j <;> rfl
  rw [he, eval_boundedRowsPredicate, wordGraph_mem_wordTreeSet]
  rfl

/-- Quantification over finite subgraphs is exactly quantification over prefixes. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Let $G_1,G_2$ be the numerical projection graphs. For a candidate word graph $w\in F$, form the bounded
    predicate
    $$\begin{aligned}
    \Theta(w):\equiv{}&\forall v\in F\;\bigl[v\IncludedIn w\ \Longrightarrow\quad
    \exists a,d\in F\;[\\
    &U(G_1,v,a)\land U(G_2,v,d)\\
    &{}\land a\in W_T\land V(a,d)]\bigr].
    \end{aligned}$$
-/
def inclusionNodePredicate : BoundedSetPredicate 18 :=
  .all 1 ((BoundedSetPredicate.subset 18 17).imply
    (inclusionTestPredicate.rename ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18]))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For actual words, graph inclusion is exactly the prefix relation. The predicates $U$ force $a,d$ to be the two
    coordinate words of that prefix, and the preceding proposition identifies $V$ with its required row tests.
    Thus $\Theta(e(w))$ holds exactly when $w\in Q(c,T)$, including the empty-prefix test.
-/
lemma eval_inclusionNodePredicate (c : BorelExpression) (T : Set (List ℕ)) (w : List ℕ)
    (bit : Bool := false) :
    inclusionNodePredicate.eval (inclusionNodeParams.{u} c T w bit) ↔ w ∈ inclusionTree c T bit := by
  simp only [inclusionNodePredicate, eval, eval_imply, eval_rename]
  change (∀ s ∈ finiteSequences, s ⊆ wordGraph w → inclusionTestPredicate.eval
    ((Fin.snoc (inclusionNodeParams c T w bit) s) ∘
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18])) ↔ _
  have he (s : List ℕ) : Fin.snoc (inclusionNodeParams.{u} c T w bit) (wordGraph s) ∘
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18] = inclusionNodeParams c T s bit := by
    funext j; fin_cases j <;> rfl
  constructor
  · intro h n hn
    have ht := h (wordGraph (w.take n)) (mem_finiteSequences.mpr ⟨_, rfl⟩)
    rw [he, eval_inclusionTestPredicate c T _ bit] at ht
    exact ht (wordGraph_subset_iff.mpr (List.take_prefix n w))
  · intro h s hs hsw
    obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hs
    rw [he, eval_inclusionTestPredicate c T _ bit]
    have hp := wordGraph_subset_iff.mp hsw
    have ht := h s.length hp.length_le
    rwa [← List.prefix_iff_eq_take.mp hp] at ht

/-- Separation uses the same reflection theorem as the individual row, with no new interpretation proof. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal counterexample node set
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    All parameters are internal. The uniform interpretation principle and Separation on $F$ now give
    $\{w\in F:\Theta(w)\}\in M$, and this set is exactly $W_{Q(c,T)}$.
-/
theorem inclusionTree_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hc : c.labelGraph ∈ M) (T : Set (List ℕ)) (hT : wordTreeSet T ∈ M) (bit : Bool := false) :
    wordTreeSet (inclusionTree c T bit) ∈ M := by
  let params : Fin 17 → M := Fin.snoc
    (fun j => ⟨finiteRowParams c bit 0 [] [] j, finiteRowParams_mem hM hinf hpair hunion hpower hsep c hc _ _ _ _ j⟩)
    ⟨wordTreeSet T, hT⟩
  have hF := finiteSequences_mem hM hinf hpair hunion hpower hsep
  apply inclusionNodePredicate.subset_mem hM (hsep _) params hF
  · intro x hx
    obtain ⟨w, _, rfl⟩ := mem_wordTreeSet.mp hx
    exact mem_finiteSequences.mpr ⟨w, rfl⟩
  · intro x hx
    obtain ⟨w, rfl⟩ := mem_finiteSequences.mp hx
    have hv : Fin.snoc (Subtype.val ∘ params) (wordGraph w) = inclusionNodeParams c T w bit := by
      funext j; fin_cases j <;> rfl
    rw [hv, eval_inclusionNodePredicate c T _ bit, wordGraph_mem_wordTreeSet]

end PolishSpaceBook.BorelExpression
