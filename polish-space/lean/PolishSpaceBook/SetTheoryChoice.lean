module

public import PolishSpaceBook.SetTheoryInternalOrderMinima
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # The Choice sentence and selectors for internal subsets

The codomain of a choice graph is the union of the family. The union is bound
explicitly, so the sentence is in the pure membership language. Its equivalence
with the usual choice-function formulation uses the model's Union axiom.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def familyNonemptyPredicate {n : ℕ} (A : Fin n) : BoundedSetPredicate n :=
  .all A (.ex (Fin.last n) (.equal (Fin.last (n + 1)) (Fin.last (n + 1))))

def familyNonemptyFormula {n : ℕ} (A : Fin n) : ForcingFormulas.Formula n :=
  (familyNonemptyPredicate A).compile

def choiceMemberPredicate {n : ℕ} (A f : Fin n) : BoundedSetPredicate n :=
  .all A (.ex (Fin.last n)
    (.pairMember f.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1))))

def choiceMemberFormula {n : ℕ} (A f : Fin n) : ForcingFormulas.Formula n :=
  (choiceMemberPredicate A f).compile

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The Choice sentence says that every family $A$ of nonempty sets admits a
    function graph $c:A\to\bigcup A$ with $c(a)\in a$ for every $a\in A$.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Choice.** For any family of nonempty sets a choice function exists: $\forall x\,(\emptyset \notin x \to \exists
        f\,(\mathrm{FunGraph}(f) \land \mathrm{dom}\, f = x \land \forall a \in x\,\, f(a) \in a))$, where
        $\mathrm{FunGraph}(f)$ abbreviates "every element of $f$ is an ordered pair, and $\langle a,b\rangle,\langle
        a,b'\rangle\in f$ implies $b=b'$."
-/
def choiceSentence : membershipLanguage.Sentence :=
  ((familyNonemptyFormula (0 : Fin 1)).imp
    (((unionFormula (0 : Fin 3) 1) ⊓ functionFormula 0 1 2 ⊓ choiceMemberFormula 0 2).ex.ex)).all

lemma realize_familyNonemptyFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (A : Fin n) (xs : Fin n → M) :
    (familyNonemptyFormula A).Realize Empty.elim xs ↔ ∀ a ∈ (xs A).val, ∃ b, b ∈ a := by
  simpa [familyNonemptyFormula, familyNonemptyPredicate, BoundedSetPredicate.eval,
    Function.comp_def, Fin.snoc] using (familyNonemptyPredicate A).realize_compile hM xs

lemma realize_choiceMemberFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (A f : Fin n) (xs : Fin n → M) :
    (choiceMemberFormula A f).Realize Empty.elim xs ↔
      ∀ a ∈ (xs A).val, ∃ b ∈ a, pair a b ∈ (xs f).val := by
  simpa [choiceMemberFormula, choiceMemberPredicate, BoundedSetPredicate.eval,
    Function.comp_def, Fin.snoc] using (choiceMemberPredicate A f).realize_compile hM xs

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    In the membership language, quantify a set $U$ satisfying $U=\bigcup A$ and use the function-graph predicate
    with codomain $U$. Union and transitivity identify this witness with the actual union.
-/
theorem models_choice_iff {M : ZFSet.{u}} (hM : M.IsTransitive) (hunion : M ⊨ unionSentence) :
    M ⊨ choiceSentence ↔ ∀ A : M, (∀ a ∈ A.val, ∃ b, b ∈ a) →
      ∃ f : M, ZFSet.IsFunc A.val (ZFSet.sUnion A.val) f.val ∧
        ∀ a ∈ A.val, ∃ b ∈ a, pair a b ∈ f.val := by
  have hf {n : ℕ} (A U f : Fin n) (xs : Fin n → M) :
      (functionFormula A U f).Realize Empty.elim xs ↔ ZFSet.IsFunc (xs A).val (xs U).val (xs f).val :=
    realize_functionFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) A U f xs
  simp only [choiceSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    Subsingleton.elim (default : Empty → M) Empty.elim]
  simp only [realize_familyNonemptyFormula hM, realize_unionFormula hM, hf, realize_choiceMemberFormula hM]
  change (∀ A : M, (∀ a ∈ A.val, ∃ b, b ∈ a) → ∃ U f : M,
    (U.val = ZFSet.sUnion A.val ∧ ZFSet.IsFunc A.val U.val f.val) ∧
      (∀ a ∈ A.val, ∃ b ∈ a, pair a b ∈ f.val)) ↔ _
  constructor
  · intro h A hA
    obtain ⟨U, f, ⟨hU, hf⟩, hs⟩ := h A hA
    exact ⟨f, hU ▸ hf, hs⟩
  · intro h A hA
    obtain ⟨f, hf, hs⟩ := h A hA
    exact ⟨⟨ZFSet.sUnion A.val, union_mem hM hunion A.property⟩, f, ⟨rfl, hf⟩, hs⟩

def internalNonemptySubsets (M W : ZFSet.{u}) : ZFSet.{u} :=
  (internalPowerSet M W).sep (fun a => ∃ b, b ∈ a)

lemma mem_internalNonemptySubsets {M W a : ZFSet.{u}} :
    a ∈ internalNonemptySubsets M W ↔ (a ∈ M ∧ a ⊆ W) ∧ ∃ b, b ∈ a := by
  simp only [internalNonemptySubsets, internalPowerSet, ZFSet.mem_sep]

lemma internalNonemptySubsets_mem {M W : ZFSet.{u}} (hM : M.IsTransitive)
    (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence (orderNonemptyFormula (0 : Fin 1))) (hW : W ∈ M) :
    internalNonemptySubsets M W ∈ M := by
  apply separation_mem_of_absolute hM (orderNonemptyFormula (0 : Fin 1)) hsep Fin.elim0
    (internalPowerSet_mem hM hpower hW) (fun a => ∃ b, b ∈ a)
  intro a _
  simpa [Fin.snoc] using realize_orderNonemptyFormula hM (0 : Fin 1) (Fin.snoc Fin.elim0 a)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal subset choice
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Internal Power Set and Separation give $S\in M$. Transitivity makes internal nonemptiness equivalent to
    actual nonemptiness, so Choice in $M$ supplies a graph $c:S\to\bigcup S$ belonging to $M$.
    The function-graph and membership predicates are absolute. Since every $r\in S$ is a subset of $W$,
    we have $\bigcup S\IncludedIn W$, and the same graph has codomain $W$.
    Only subsets belonging to $M$ are inputs to this graph.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To construct an internal well-order, first obtain a single choice graph for all nonempty internal subsets.
-/
theorem internal_subset_choice {M W : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence (orderNonemptyFormula (0 : Fin 1)))
    (hchoice : M ⊨ choiceSentence) (hW : W ∈ M) :
    ∃ c : M, ZFSet.IsFunc (internalNonemptySubsets M W) W c.val ∧
      ∀ a ∈ internalNonemptySubsets M W, ∃ b ∈ a, pair a b ∈ c.val := by
  let S : M := ⟨internalNonemptySubsets M W, internalNonemptySubsets_mem hM hpower hsep hW⟩
  obtain ⟨c, hc, hs⟩ := (models_choice_iff hM hunion).mp hchoice S
    (fun a ha => (mem_internalNonemptySubsets.mp ha).2)
  refine ⟨c, ⟨?_, hc.2⟩, hs⟩
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp (hc.1 hp)
  obtain ⟨s, hsS, hbs⟩ := ZFSet.mem_sUnion.mp hb
  exact ZFSet.pair_mem_prod.mpr ⟨ha, (mem_internalNonemptySubsets.mp hsS).1.2 hbs⟩

end PolishSpaceBook.SetTheoryModels
