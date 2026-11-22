module

public import PolishSpaceBook.SetTheoryChoice

@[expose] public section

/-! # Internal selectors of minimal elements of a well-founded relation

The minimum hypothesis quantifies only over subsets in the model. Applying an
internal subset selector to the set of minimal elements produces a selector
that respects the relation, without assuming external well-foundedness.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def minimalMemberPredicate {n : ℕ} (A R x : Fin n) : BoundedSetPredicate n :=
  .all A (.neg (.pairMember R.castSucc (Fin.last n) x.castSucc))

def minimalMemberFormula {n : ℕ} (A R x : Fin n) : ForcingFormulas.Formula n :=
  (minimalMemberPredicate A R x).compile

lemma minimalMemberFormula_deltaZero {n : ℕ} (A R x : Fin n) :
    IsDeltaZero (minimalMemberFormula A R x) :=
  (minimalMemberPredicate A R x).compile_deltaZero

def minimalSet (R A : ZFSet.{u}) : ZFSet.{u} :=
  A.sep (fun x => ∀ y ∈ A, pair y x ∉ R)

lemma mem_minimalSet {R A x : ZFSet.{u}} :
    x ∈ minimalSet R A ↔ x ∈ A ∧ ∀ y ∈ A, pair y x ∉ R := ZFSet.mem_sep

lemma realize_minimalMemberFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (A R x : Fin n) (xs : Fin n → M) :
    (minimalMemberFormula A R x).Realize Empty.elim xs ↔
      ∀ y ∈ (xs A).val, pair y (xs x).val ∉ (xs R).val := by
  simpa [minimalMemberFormula, minimalMemberPredicate, BoundedSetPredicate.eval,
    Function.comp_def, Fin.snoc] using (minimalMemberPredicate A R x).realize_compile hM xs

lemma minimalSet_mem {M R A : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hR : R ∈ M) (hA : A ∈ M) : minimalSet R A ∈ M := by
  apply separation_mem_of_absolute hM (minimalMemberFormula (0 : Fin 3) 1 2) (hsep _)
    ![⟨A, hA⟩, ⟨R, hR⟩] hA
  intro x _
  simpa [Fin.snoc] using
    realize_minimalMemberFormula hM (0 : Fin 3) 1 2 (Fin.snoc ![⟨A, hA⟩, ⟨R, hR⟩] x)

/-- Equality with the minimal-element set has a bounded membership-language definition. -/
def minimalSetPredicate {n : ℕ} (A R V : Fin n) : BoundedSetPredicate n :=
  .conj (.subset V A) (.all A
    (.iff (.member (Fin.last n) V.castSucc)
      (minimalMemberPredicate A.castSucc R.castSucc (Fin.last n))))

def minimalSetFormula {n : ℕ} (A R V : Fin n) : ForcingFormulas.Formula n :=
  (minimalSetPredicate A R V).compile

lemma minimalSetFormula_deltaZero {n : ℕ} (A R V : Fin n) :
    IsDeltaZero (minimalSetFormula A R V) :=
  (minimalSetPredicate A R V).compile_deltaZero

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The equality $V=m_R(U)$ is expressed by the bounded formula
    $$V\IncludedIn U\;\land\;\forall x\in U\;
    \bigl(x\in V\;\longleftrightarrow\;\forall y\in U\;\langle y,x\rangle\notin R\bigr).$$
-/
lemma realize_minimalSetFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (A R V : Fin n) (xs : Fin n → M) :
    (minimalSetFormula A R V).Realize Empty.elim xs ↔
      (xs V).val = minimalSet (xs R).val (xs A).val := by
  rw [minimalSetFormula, BoundedSetPredicate.realize_compile hM]
  simp only [minimalSetPredicate, minimalMemberPredicate, BoundedSetPredicate.eval,
    Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨hVA, h⟩
    apply ZFSet.ext
    intro x
    rw [mem_minimalSet]
    exact ⟨fun hx => ⟨hVA hx, (h x (hVA hx)).mp hx⟩,
      fun hx => (h x hx.1).mpr hx.2⟩
  · intro h
    rw [h]
    exact ⟨fun _ hx => (mem_minimalSet.mp hx).1,
      fun x hx => ⟨fun hv => (mem_minimalSet.mp hv).2,
        fun hm => mem_minimalSet.mpr ⟨hx, hm⟩⟩⟩

/-- Parameters S,W,R,c,p; the output p pairs an input A with c(minimalSet R A). -/
def minimumSelectorFormula : ForcingFormulas.Formula 5 :=
  boundedExists 0 (boundedExists 1
    ((orderedPairFormula (4 : Fin 8) 5 6 ⊓ minimalSetFormula 5 2 7 ⊓
      pairMemberFormula 3 7 6).ex))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    $$c(U):=c_0(m_R(U)).$$
-/
def minimumSelectorGraph (S W R c : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod S W).sep (fun p =>
    ∃ A ∈ S, ∃ x ∈ W, p = pair A x ∧ pair (minimalSet R A) x ∈ c)

lemma pair_mem_minimumSelectorGraph {S W R c A x : ZFSet.{u}} :
    pair A x ∈ minimumSelectorGraph S W R c ↔
      A ∈ S ∧ x ∈ W ∧ pair (minimalSet R A) x ∈ c := by
  rw [minimumSelectorGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hA, hx⟩, B, _, y, _, he, hp⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hA, hx, hp⟩
  · rintro ⟨hA, hx, hp⟩
    exact ⟨⟨hA, hx⟩, A, hA, x, hx, rfl, hp⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Thus the separating formula has parameters in $M$, and its required witness $V=m_R(U)$ belongs to $M$.
-/
lemma realize_minimumSelectorFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (S W R c p : M) :
    minimumSelectorFormula.Realize Empty.elim ![S, W, R, c, p] ↔
      ∃ A ∈ S.val, ∃ x ∈ W.val, p.val = pair A x ∧ pair (minimalSet R.val A) x ∈ c.val := by
  have hp {n : ℕ} (q a b : Fin n) (xs : Fin n → M) :
      (orderedPairFormula q a b).Realize Empty.elim xs ↔
        (xs q).val = pair (xs a).val (xs b).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q a b xs
  simp only [minimumSelectorFormula, realize_boundedExists_model, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, hp, realize_minimalSetFormula hM,
    realize_pairMemberFormula_model hM, Fin.snoc]
  constructor
  · rintro ⟨A, hA, x, hx, V, ⟨he, hV⟩, hp⟩
    exact ⟨A.val, hA, x.val, hx, he, hV ▸ hp⟩
  · rintro ⟨A, hA, x, hx, he, hp⟩
    have hAM := hM.mem_trans hA S.property
    exact ⟨⟨A, hAM⟩, hA, ⟨x, hM.mem_trans hx W.property⟩, hx,
      ⟨minimalSet R.val A, minimalSet_mem hM hsep R.property hAM⟩, ⟨he, rfl⟩, hp⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    To obtain the whole graph internally, separate from $S\times W$ the pairs $\langle U,x\rangle$ satisfying
    $$\exists V\;\bigl(V=m_R(U)\land\langle V,x\rangle\in c_0\bigr).$$
-/
lemma minimumSelectorGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (S W R c : M) : minimumSelectorGraph S.val W.val R.val c.val ∈ M := by
  apply separation_mem_of_absolute hM minimumSelectorFormula (hsep _) ![S, W, R, c]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) S.property W.property)
  intro p _
  have hs : Fin.snoc ![S, W, R, c] p = ![S, W, R, c, p] := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  exact realize_minimumSelectorFormula hM hsep S W R c p

/-- Choose a relation-minimal member of each nonempty internal subset. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal selection of relation-minimal elements
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The internal subset-choice lemma in §{sec:internal-choice-recursion} gives $S\in M$ and a selector
    $c_0:S\to W$ in $M$. For $U\in S$, define
    $$m_R(U):=\{x\in U:\forall y\in U\;\langle y,x\rangle\notin R\}.$$
    Its defining predicate is bounded, so Separation gives $m_R(U)\in M$. The assertion $M\models\chi(W,R)$ makes it
    nonempty, and $m_R(U)\IncludedIn U\IncludedIn W$ gives $m_R(U)\in S$. Put
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The unique value of $c_0$ therefore makes
    the separated set a total function graph on $S$. Its values belong to $m_R(U)$, proving both assertions.
-/
theorem internal_minimum_selector {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hchoice : M ⊨ choiceSentence) (W R : M)
    (hmin : internalOrderMinimaFormula.Realize Empty.elim ![W, R]) :
    ∃ c : M, IsFunc (internalNonemptySubsets M W.val) W.val c.val ∧
      (∀ A ∈ internalNonemptySubsets M W.val, ∃ x ∈ A, pair A x ∈ c.val) ∧
      (∀ A ∈ internalNonemptySubsets M W.val, ∀ x, pair A x ∈ c.val →
        ∀ y ∈ A, pair y x ∉ R.val) := by
  obtain ⟨c₀, hc₀, hs₀⟩ := internal_subset_choice hM hunion hpower (hsep _) hchoice W.property
  let S : M := ⟨internalNonemptySubsets M W.val, internalNonemptySubsets_mem hM hpower (hsep _) W.property⟩
  have hV (A : ZFSet.{u}) (hA : A ∈ S.val) : minimalSet R.val A ∈ S.val := by
    obtain ⟨⟨hAM, hAW⟩, hne⟩ := mem_internalNonemptySubsets.mp hA
    obtain ⟨x, hx, hxmin⟩ := (realize_internalOrderMinimaFormula hM W R).mp hmin ⟨A, hAM⟩ hAW hne
    exact mem_internalNonemptySubsets.mpr
      ⟨⟨minimalSet_mem hM hsep R.property hAM, fun _ h => hAW (mem_minimalSet.mp h).1⟩,
        x, mem_minimalSet.mpr ⟨hx, hxmin⟩⟩
  let c : M := ⟨minimumSelectorGraph S.val W.val R.val c₀.val,
    minimumSelectorGraph_mem hM hpair hunion hpower hsep S W R c₀⟩
  have hsel (A : ZFSet.{u}) (hA : A ∈ S.val) :
      ∃ x ∈ minimalSet R.val A, pair A x ∈ c.val := by
    obtain ⟨x, hx, hpx⟩ := hs₀ _ (hV A hA)
    exact ⟨x, hx, pair_mem_minimumSelectorGraph.mpr
      ⟨hA, (mem_internalNonemptySubsets.mp hA).1.2 (mem_minimalSet.mp hx).1, hpx⟩⟩
  refine ⟨c, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    change p ∈ minimumSelectorGraph S.val W.val R.val c₀.val at hp
    exact (ZFSet.mem_sep.mp hp).1
  · intro A hA
    obtain ⟨x, _, hx⟩ := hsel A hA
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact (hc₀.2 _ (hV A hA)).unique
      (pair_mem_minimumSelectorGraph.mp hy).2.2 (pair_mem_minimumSelectorGraph.mp hx).2.2
  · intro A hA
    obtain ⟨x, hx, hp⟩ := hsel A hA
    exact ⟨x, (mem_minimalSet.mp hx).1, hp⟩
  · intro A hA x hx
    obtain ⟨y, hy, hpy⟩ := hs₀ _ (hV A hA)
    have he : x = y := (hc₀.2 _ (hV A hA)).unique
      (pair_mem_minimumSelectorGraph.mp hx).2.2 hpy
    exact he ▸ (mem_minimalSet.mp hy).2

end PolishSpaceBook.SetTheoryModels
