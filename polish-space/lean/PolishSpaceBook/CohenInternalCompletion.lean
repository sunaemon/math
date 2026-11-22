module

public import PolishSpaceBook.ForcingRegularEmbedding
public import PolishSpaceBook.InternalCohenConditions
public import PolishSpaceBook.CohenRegularOpenCompletion

@[expose] public section

/-! # The internally computed Cohen completion and its represented embedding -/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels ForcingAtomic CantorTreeMeasure
universe u

abbrev cohenCodePartialOrder : PartialOrder (Condition (cohenConditionSet.{u} Set.univ)) where
  toPreorder := internalCohenOrder
  le_antisymm _ _ hpq hqp := condition_eq_of_val_eq (le_antisymm hqp hpq)

local instance : PartialOrder (Condition (cohenConditionSet.{u} Set.univ)) := cohenCodePartialOrder

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $e(p)=\{q\in P:q\le p\}$. If $q\not\le p$, the cylinder order embedding gives
    $\neg(\cyl{q}\IncludedIn\cyl{p})$. Their nonempty clopen difference contains a cylinder $\cyl{r}$.
    Thus $r\le q$ and $r$ is incompatible with $p$.
-/
lemma cohenCode_separative (p q : Condition (cohenConditionSet.{u} Set.univ)) (hpq : ¬ p ≤ q) :
    ∃ r ≤ p, incompatible (cohenConditionSet Set.univ) r q := by
  obtain ⟨s, rfl⟩ := cohenCodedCondition_surjective p
  obtain ⟨t, rfl⟩ := cohenCodedCondition_surjective q
  have hst : ¬cohenCylinder s ≤ cohenCylinder t := by
    intro h
    exact hpq ((cohenCodedCondition_le_iff t s).mpr ((cohenCylinder_le_iff s t).mp h))
  have hne : cohenCylinder s ⊓ (cohenCylinder t)ᶜ ≠ ⊥ := by
    intro hz
    apply hst
    calc
      cohenCylinder s = cohenCylinder s ⊓ cohenCylinder t ⊔ cohenCylinder s ⊓ (cohenCylinder t)ᶜ := sup_inf_inf_compl.symm
      _ = cohenCylinder s ⊓ cohenCylinder t := by rw [hz, sup_bot_eq]
      _ ≤ cohenCylinder t := inf_le_right
  obtain ⟨r, hr⟩ := cohenCylinder_dense _ hne
  refine ⟨cohenCodedCondition r, (cohenCodedCondition_le_iff s r).mpr
    ((cohenCylinder_le_iff r s).mp (hr.trans inf_le_left)), ?_⟩
  rintro ⟨v, hvr, hvt⟩
  obtain ⟨v, rfl⟩ := cohenCodedCondition_surjective v
  have h₁ := (cohenCylinder_le_iff v r).mpr ((cohenCodedCondition_le_iff r v).mp hvr)
  have h₂ := (cohenCylinder_le_iff v t).mpr ((cohenCodedCondition_le_iff t v).mp hvt)
  exact cohenCylinder_ne_bot v (le_bot_iff.mp ((le_inf h₂ (h₁.trans (hr.trans inf_le_right))).trans_eq (inf_compl_self _)))

def cohenOrderGraphPredicate : BoundedSetPredicate 2 :=
  .ex 0 (.ex 0 (.conj (.orderedPair 1 2 3) (.subset 3 2)))

def cohenOrderGraph (P : ZFSet.{u}) : ZFSet.{u} :=
  (prod P P).sep (fun z => cohenOrderGraphPredicate.eval ![P, z])

lemma cohenOrderGraph_correct (p q : Condition (cohenConditionSet.{u} Set.univ)) :
    pair p.val q.val ∈ cohenOrderGraph (cohenConditionSet Set.univ) ↔ p ≤ q := by
  change _ ↔ q.val ⊆ p.val
  simp [cohenOrderGraph, cohenOrderGraphPredicate, BoundedSetPredicate.eval, Fin.snoc, Fin.castLT,
    Fin.castPred, pair_inj, p.property, q.property]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hpair hunion hpower hsep in
lemma cohenOrderGraph_mem (P : M) : cohenOrderGraph P.val ∈ M := by
  have he (z : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P]) z = ![P.val, z] := by
    funext i; fin_cases i <;> rfl
  simpa only [cohenOrderGraph, he] using cohenOrderGraphPredicate.separation_mem hM (hsep _) ![P]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) P.property P.property)

abbrev cohenConditionsInModel : M :=
  ⟨cohenConditionSet Set.univ, binaryWords_mem hM hinf hpair hunion hpower hsep⟩

abbrev cohenOrderInModel : M :=
  ⟨cohenOrderGraph (cohenConditionSet Set.univ),
    cohenOrderGraph_mem hM hpair hunion hpower hsep (cohenConditionsInModel hM hinf hpair hunion hpower hsep)⟩

local notation "P" => cohenConditionsInModel hM hinf hpair hunion hpower hsep
local notation "R" => cohenOrderInModel hM hinf hpair hunion hpower hsep

abbrev cohenCompletionCarrier : M := regularCarrierInModel hM hpower hsep P R

abbrev cohenCompletionBooleanAlgebra : BooleanAlgebra (BooleanElement (cohenCompletionCarrier hM hinf hpair hunion hpower hsep).val) :=
  internalRegularBooleanAlgebra hM hinf hpair hunion hsep P R cohenOrderGraph_correct

def cohenCompletionAlgebra :
    letI := cohenCompletionBooleanAlgebra hM hinf hpair hunion hpower hsep
    InternalBooleanAlgebra (cohenCompletionCarrier hM hinf hpair hunion hpower hsep) :=
  internalRegularAlgebra hM hinf hpair hunion hpower hsep P R cohenOrderGraph_correct

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{proposition*}[Cohen completion and generic filters]
    The finite binary-string order $P$ has a dense order embedding $e:P\to\mathbb B^+$ into its
    internally computed regular-set completion, with the graph of $e$ belonging to $M$.
    It induces a bijection between the $M$-generic filters on the two orders.
    \end{proposition*}
-/
def cohenCompletionEmbedding :
    letI := cohenCompletionBooleanAlgebra hM hinf hpair hunion hpower hsep
    Condition (cohenConditionSet Set.univ) ↪o Condition
      (InternalBooleanAlgebra.positiveSet (cohenCompletionCarrier hM hinf hpair hunion hpower hsep)) :=
  regularCompletionEmbedding hM hinf hpair hunion hpower hsep P R cohenOrderGraph_correct cohenCode_separative

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Thus the principal lower set $e(p)$ is regular. It is nonempty, and
    $e(p)\IncludedIn e(q)$ holds exactly when $p\le q$. Every nonempty regular lower set contains
    some $p$ and therefore contains $e(p)$. This proves density.
-/
theorem cohenCompletionEmbedding_dense :
    letI := cohenCompletionBooleanAlgebra hM hinf hpair hunion hpower hsep
    ∀ b, ∃ p, cohenCompletionEmbedding hM hinf hpair hunion hpower hsep p ≤ b :=
  regularCompletionEmbedding_dense hM hinf hpair hunion hpower hsep P R cohenOrderGraph_correct cohenCode_separative

abbrev cohenEmbeddingGraphInModel : M :=
  ⟨regularEmbeddingGraph (P).val (R).val (cohenCompletionCarrier hM hinf hpair hunion hpower hsep).val,
    regularEmbeddingGraph_mem hM hpair hunion hpower hsep P R
      (cohenCompletionCarrier hM hinf hpair hunion hpower hsep)⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    The defining formula for the graph
    has only bounded quantifiers over $P$, so Separation puts that graph in $M$.
-/
lemma cohenCompletionEmbedding_represented :
    letI := cohenCompletionBooleanAlgebra hM hinf hpair hunion hpower hsep
    ∀ p b, pair p.val b.val ∈ (cohenEmbeddingGraphInModel hM hinf hpair hunion hpower hsep).val ↔
      cohenCompletionEmbedding hM hinf hpair hunion hpower hsep p = b :=
  regularCompletionEmbedding_graph hM hinf hpair hunion hpower hsep P R cohenOrderGraph_correct cohenCode_separative

end PolishSpaceBook
