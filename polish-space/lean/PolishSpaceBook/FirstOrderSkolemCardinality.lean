module

public import PolishSpaceBook.FirstOrderLowenheimSkolem

@[expose] public section

/-!
# Cardinal bounds on the explicitly constructed Skolem hull

An infinite bound is preserved by each finite-arity closure step and by the
countable union of stages. The bound counts function symbols and finite tuples,
including nullary functions, rather than using an abstract closure theorem.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language Cardinal
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- An infinite cardinal bound survives one closure step. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Use the same stages as above, starting with $B_0=X\cup\{a_0\}$, whose size is at most $\kappa$.
    For every finite arity $r$, one has $\kappa^r\le\kappa$, including $r=0$. If $|B_n|\le\kappa$, then
    $$\begin{aligned}
    |B_{n+1}|&\le |B_n|+\sum_{F\in\mathcal F}|B_n|^{r(F)}\\
    &\le\kappa+\kappa\cdot\kappa=\kappa.
    \end{aligned}$$
-/
theorem card_operationStep_le (κ : Cardinal.{max u w}) (hκ : ℵ₀ ≤ κ)
    (hF : lift.{w} #(Σ n, L.Functions n) ≤ κ) {A : Set M} (hA : lift.{u} #A ≤ κ) :
    lift.{u} #(operationStep L A) ≤ κ := by
  let R (f : Σ n, L.Functions n) : Set M :=
    Set.range (fun s : Fin f.1 → A => Structure.funMap f.2 (Subtype.val ∘ s))
  have hr (f : Σ n, L.Functions n) : lift.{u} #(R f) ≤ κ := by
    apply (lift_le.mpr mk_range_le).trans
    calc
      lift.{u} #(Fin f.1 → A) = (lift.{u} #A) ^ (f.1 : Cardinal) := by
        rw [mk_arrow, lift_power]
        simp
      _ ≤ κ ^ (f.1 : Cardinal) := power_le_power_right hA
      _ ≤ κ := power_nat_le hκ
  have hU : lift.{u} #(⋃ f, R f) ≤ κ := by
    apply (mk_iUnion_le_lift R).trans
    exact (mul_le_mul' hF (ciSup_le' hr)).trans (le_of_eq (mul_eq_self hκ))
  apply (lift_le.mpr (mk_union_le A (⋃ f, R f))).trans
  rw [lift_add]
  exact (add_le_add hA hU).trans (le_of_eq (add_eq_self hκ))

theorem card_operationStages_le (κ : Cardinal.{max u w}) (hκ : ℵ₀ ≤ κ)
    (hF : lift.{w} #(Σ n, L.Functions n) ≤ κ) {X : Set M} (hX : lift.{u} #X ≤ κ) (n : ℕ) :
    lift.{u} #(operationStages L X n) ≤ κ := by
  induction n with
  | zero => exact hX
  | succ n ih => exact card_operationStep_le κ hκ hF ih

/-- Countably many bounded stages remain bounded by the same infinite cardinal. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induction bounds every stage, and the countable union satisfies
    $$|B|\le\alephNull\cdot\kappa=\kappa.$$
    The closure argument and the \termuse{Tarski--Vaught test} apply as before: each finite parameter tuple lies
    in a single stage, and its chosen witness lies in the next stage.
-/
theorem card_operationSubstructure_le (κ : Cardinal.{max u w}) (hκ : ℵ₀ ≤ κ)
    (hF : lift.{w} #(Σ n, L.Functions n) ≤ κ) {X : Set M} (hX : lift.{u} #X ≤ κ) :
    lift.{u} #(operationSubstructure (L := L) X) ≤ κ := by
  change lift.{u} #(⋃ n, operationStages L X n) ≤ κ
  have h := mk_iUnion_le_lift (operationStages L X)
  have h' := lift_le.{u}.mpr h
  simp only [lift_lift, lift_mul, lift_iSup bddAbove_of_small, lift_aleph0, mk_nat] at h'
  apply h'.trans
  exact (mul_le_mul' hκ (ciSup_le' (card_operationStages_le κ hκ hF hX))).trans
    (le_of_eq (mul_eq_self hκ))

/-- The same Skolem stage model satisfies every infinite bound on the seed and language. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The symbols of $L$, the variable names, and the logical constructors form an alphabet of size at most $\kappa$.
    Finite expressions over this alphabet also number at most $\kappa$. In particular, there are at most $\kappa$
    formulas and hence at most $\kappa$ chosen Skolem functions. Adding the original function interpretations still
    leaves $|\mathcal F|\le\kappa$.
-/
theorem card_skolemStageModel_le [Nonempty M] (κ : Cardinal.{max u v w}) (hκ : ℵ₀ ≤ κ)
    (hL : lift.{w} L.card ≤ κ) {X : Set M} (hX : lift.{max u v} #X ≤ κ) :
    lift.{max u v} #(skolemStageModel (L := L) X) ≤ κ := by
  have hF : lift.{w} #(Σ n, (L.sum L.skolem₁).Functions n) ≤ κ := by
    apply (lift_le.mpr (card_functions_sum_skolem₁_le (L := L))).trans
    simpa only [lift_max, lift_aleph0] using max_le hκ hL
  have hseed : lift.{max u v} #(insert (Classical.choice ‹Nonempty M›) X : Set M) ≤ κ := by
    apply (lift_le.mpr mk_insert_le).trans
    rw [lift_add, lift_one]
    exact (add_le_add hX (one_le_aleph0.trans hκ)).trans (le_of_eq (add_eq_self hκ))
  exact card_operationSubstructure_le κ hκ hF hseed

/-- The general bound with an arbitrary infinite cardinal and a prescribed seed. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Cardinal bound for elementary substructures
-/
theorem exists_elementarySubstructure_card_le_of_bounds [Nonempty M] (κ : Cardinal.{max u v w})
    (hκ : ℵ₀ ≤ κ) (hL : lift.{w} L.card ≤ κ) {X : Set M} (hX : lift.{max u v} #X ≤ κ) :
    ∃ B : L.ElementarySubstructure M, X ⊆ B ∧ lift.{max u v} #B ≤ κ :=
  ⟨skolemStageModel X, subset_skolemStageModel X, card_skolemStageModel_le κ hκ hL hX⟩

/-- The general downward upper bound, for the explicitly constructed elementary substructure. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Taking $\kappa=\max(|L|,|X|,\alephNull)$ gives the general downward bound. For a consistent $L$-theory,
    $\kappa=\max(|L|,\alephNull)$ already suffices. A separate factor for $|T|$ is unnecessary: a theory is a set of
    sentences, and the total number of $L$-sentences is at most this same bound.
-/
theorem exists_elementarySubstructure_card_le [Nonempty M] (X : Set M) :
    ∃ B : L.ElementarySubstructure M, X ⊆ B ∧
      lift.{max u v} #B ≤ max ℵ₀ (max (lift.{w} L.card) (lift.{max u v} #X)) := by
  refine ⟨skolemStageModel X, subset_skolemStageModel X, ?_⟩
  exact card_skolemStageModel_le _ (le_max_left _ _) (le_max_of_le_right (le_max_left _ _))
    (le_max_of_le_right (le_max_right _ _))

end PolishSpaceBook.NamedFirstOrder
