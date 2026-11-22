module

public import PolishSpaceBook.BorelExpressionConstructors
public import PolishSpaceBook.BorelInternalInterpretation
public import PolishSpaceBook.SetTheoryWordCons
public import PolishSpaceBook.SetTheoryFunctionClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Re-rooting Borel expressions without changing their node interpretations -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Remove a fixed initial segment from the addresses below a node. -/
def below (c : BorelExpression) (s : List ℕ) : BorelExpression := fun t => c (s ++ t)

lemma wellFounded_below (c : BorelExpression) (hw : WellFounded c.Child) (s : List ℕ) :
    WellFounded (c.below s).Child := by
  apply (InvImage.wf (fun t => s ++ t) hw).mono
  rintro t v ⟨hv, k, rfl, ht⟩
  exact ⟨hv, k, (List.append_assoc _ _ _).symm, ht⟩

lemma valid_below (c : BorelExpression) (hc : c.Valid) (s : List ℕ) (hs : c s ≠ 0) :
    (c.below s).Valid := by
  refine ⟨by simpa [below] using hs, ?_, ?_, ?_, ?_, wellFounded_below c hc.2.2.2.2.2 s⟩
  · intro t k ht
    exact hc.2.1 (s ++ t) k (by simpa [below, List.append_assoc] using ht)
  · intro t ht k
    simpa [below, List.append_assoc] using hc.2.2.1 (s ++ t) ht k
  · intro t ht
    simpa [below, List.append_assoc] using hc.2.2.2.1 (s ++ t) ht
  · intro t ht
    simpa [below, List.append_assoc] using hc.2.2.2.2.1 (s ++ t) ht

lemma evaluate_below {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set X) (s t : List ℕ) :
    (c.below s).evaluate (wellFounded_below c hw s) U t = c.evaluate hw U (s ++ t) := by
  have h : (c.below s).SetEvaluation U (fun t => c.evaluate hw U (s ++ t)) := by
    intro v
    simpa only [below, List.append_assoc] using c.evaluate_isEvaluation hw U (s ++ v)
  exact congrFun (((c.below s).evaluate_isEvaluation (wellFounded_below c hw s) U).unique
    (wellFounded_below c hw s) h) t

/-- A fixed valid expression for the empty set, when basic set zero is the whole space. -/
def emptyExpression : BorelExpression := complement (basic 0)

lemma valid_emptyExpression : emptyExpression.Valid := valid_complement _ (valid_basic 0)

lemma evaluate_emptyExpression {X : Type*} (U : ℕ → Set X) (hU : U 0 = Set.univ) :
    emptyExpression.evaluate valid_emptyExpression.2.2.2.2.2 U [] = ∅ := by
  change (complement (basic 0)).denotes (valid_complement _ (valid_basic 0)) U = _
  rw [denotes_complement U (basic 0) (valid_basic 0), denotes_basic, hU, Set.compl_univ]

/-- An absent node is represented by the fixed valid empty expression. -/
def nodeCode (c : BorelExpression) (s : List ℕ) : BorelExpression :=
  if c s = 0 then emptyExpression else c.below s

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For a present node, take $\eta_s(t)=c(s\concat t)$. Its child relation maps into the child relation of $c$
    by prepending $s$, so it is well-founded; the local validity clauses are inherited. Restricting the
    set evaluation of $c$ to these addresses satisfies the evaluation equations for $\eta_s$. Uniqueness of
    well-founded evaluation gives the asserted equality at the root, and restricting to old points gives
    the internal equality.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    If $c(s)=0$, its evaluation is empty. Use the fixed valid empty code
    $$\eta_\varnothing:=\BorelComplementCode{\BorelLeafCode{0}}.$$
    Its labels are $2$ at $[]$, $3$ at $[0]$, and $0$ elsewhere. Equality with these two finite words gives a
    bounded definition of every label, so the same graph-collection principle puts its label graph in $M$.
    Its root evaluates to the complement of the whole space. Thus $\eta_s=\eta_\varnothing$ has both required
    interpretations in this case as well.
-/
lemma valid_nodeCode (c : BorelExpression) (hc : c.Valid) (s : List ℕ) : (c.nodeCode s).Valid := by
  unfold nodeCode
  split_ifs with hs
  · exact valid_emptyExpression
  · exact valid_below c hc s hs

lemma evaluate_eq_of_code_eq {X : Type*} (c d : BorelExpression)
    (hc : WellFounded c.Child) (hd : WellFounded d.Child) (h : c = d)
    (U : ℕ → Set X) (s : List ℕ) : c.evaluate hc U s = d.evaluate hd U s := by
  subst d
  rfl

lemma evaluate_nodeCode {X : Type*} (c : BorelExpression) (hc : c.Valid)
    (U : ℕ → Set X) (hU : U 0 = Set.univ) (s : List ℕ) :
    (c.nodeCode s).evaluate (valid_nodeCode c hc s).2.2.2.2.2 U [] =
      c.evaluate hc.2.2.2.2.2 U s := by
  by_cases hs : c s = 0
  · have he : c.nodeCode s = emptyExpression := ite_eq_left hs
    rw [evaluate_eq_of_code_eq _ _ _ valid_emptyExpression.2.2.2.2.2 he,
      evaluate_emptyExpression U hU, c.evaluate_isEvaluation]
    simp [hs]
  · have he : c.nodeCode s = c.below s := ite_eq_right hs
    rw [evaluate_eq_of_code_eq _ _ _ (wellFounded_below c hc.2.2.2.2.2 s) he, evaluate_below,
      List.append_nil]

lemma labelGraph_eq_functionGraph (c : BorelExpression) :
    c.labelGraph = functionGraph (fun s : (finiteSequences : ZFSet.{u}) =>
      natOrdinal (c (wordEquiv.symm s))) := by
  ext p
  simp only [labelGraph, functionGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨wordEquiv s, by simp⟩
  · rintro ⟨s, rfl⟩
    exact ⟨wordEquiv.symm s, by rw [show wordGraph (wordEquiv.symm s) = s.val from
      congrArg Subtype.val (wordEquiv.apply_symm_apply s)]⟩

/-- A bounded value definition collects the entire label graph by the shared reflection theorem. -/
lemma bounded_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {k : ℕ} (p : BoundedSetPredicate (k + 2)) (ps : Fin k → M) (c : BorelExpression)
    (hp : ∀ s, ∀ a : M, p.eval (Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (wordGraph s)) a.val) ↔
      a.val = natOrdinal (c s)) : c.labelGraph ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  let f (s : (finiteSequences : ZFSet.{u})) : M := ⟨natOrdinal (c (wordEquiv.symm s)), hn _⟩
  rw [labelGraph_eq_functionGraph]
  apply replacement_graph_mem hM hpair p.compile (hrep _) ps
    (finiteSequences_mem hM hinf hpair hunion hpower hsep) f
  intro s a
  rw [p.realize_compile hM]
  simp only [Fin.comp_snoc]
  rw [← show wordGraph (wordEquiv.symm s) = s.val from
    congrArg Subtype.val (wordEquiv.apply_symm_apply s), hp]
  constructor
  · intro he
    apply Subtype.ext
    exact he
  · intro he
    exact congrArg Subtype.val he

/-- Parameters omega, zero, head, finite words, original labels, input word, output label. -/
def belowHeadPredicate : BoundedSetPredicate 7 :=
  .ex 3 (.conj (wordConsPredicate.rename ![0, 1, 2, 5, 7]) (.pairMember 4 7 6))

lemma eval_belowHeadPredicate (c : BorelExpression) (a : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    belowHeadPredicate.eval ![Ordinal.omega0.toZFSet, natOrdinal 0, natOrdinal a, finiteSequences,
      c.labelGraph, wordGraph s, y] ↔ y = natOrdinal (c (a :: s)) := by
  simp only [belowHeadPredicate, eval, eval_rename, Fin.snoc]
  change (∃ t ∈ finiteSequences,
    SetWordCons Ordinal.omega0.toZFSet (natOrdinal 0) (natOrdinal a) (wordGraph s) t ∧
      pair t y ∈ c.labelGraph) ↔ _
  constructor
  · rintro ⟨t, ht, hcons, hy⟩
    obtain ⟨v, rfl⟩ := mem_finiteSequences.mp ht
    rw [setWordCons_wordGraph_iff] at hcons
    rwa [hcons, pair_mem_labelGraph] at hy
  · intro hy
    exact ⟨wordGraph (a :: s), mem_finiteSequences.mpr ⟨_, rfl⟩,
      (setWordCons_wordGraph_iff _ _ _).mpr rfl, (pair_mem_labelGraph _ _ _).mpr hy⟩

lemma below_head_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (c : BorelExpression) (hc : c.labelGraph ∈ M) (a : ℕ) : (c.below [a]).labelGraph ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let F : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let ps : Fin 5 → M := ![Ω, ⟨natOrdinal 0, hn 0⟩, ⟨natOrdinal a, hn a⟩, F, ⟨c.labelGraph, hc⟩]
  apply bounded_labelGraph_mem hM hinf hpair hunion hpower hsep hrep belowHeadPredicate ps (c.below [a])
  intro s y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (wordGraph s)) y.val =
      ![Ordinal.omega0.toZFSet, natOrdinal 0, natOrdinal a, finiteSequences, c.labelGraph, wordGraph s, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_belowHeadPredicate]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    To construct the whole label graph internally, first prepend just one entry $a$. With $K$ from
    §{sec:internal-list-coding}, the bounded condition
    $$\exists \tau\in F\;[K(a,\sigma,\tau)\land\Pair{\tau}{j}\in\ell]$$
    recognizes $j=c(a::t)$ when $\sigma=e(t)$. The shared interpretation and graph-collection principles put this
    label graph in $M$. Repeating the operation along the finitely many entries of $s$ gives the graph of
    $\eta_s$. This proves internality of the entire graph, rather than just its individual values.
-/
lemma below_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (c : BorelExpression) (hc : c.labelGraph ∈ M) (s : List ℕ) : (c.below s).labelGraph ∈ M := by
  induction s generalizing c with
  | nil => exact hc
  | cons a s ih =>
    exact ih (c.below [a]) (below_head_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc a)

lemma emptyExpression_apply (s : List ℕ) :
    emptyExpression s = if s = [] then 2 else if s = [0] then 3 else 0 := by
  cases s with
  | nil => rfl
  | cons a s =>
    cases s <;> by_cases ha : a = 0 <;> simp [emptyExpression, complement_cons, basic, ha]

/-- Parameters zero, two, three, empty word, word [0], input word, output label. -/
def emptyLabelPredicate : BoundedSetPredicate 7 :=
  .disj (.conj (.equal 5 3) (.equal 6 1))
    (.disj (.conj (.equal 5 4) (.equal 6 2))
      (.conj (.neg (.equal 5 3)) (.conj (.neg (.equal 5 4)) (.equal 6 0))))

lemma eval_emptyLabelPredicate (s : List ℕ) (y : ZFSet.{u}) :
    emptyLabelPredicate.eval ![natOrdinal 0, natOrdinal 2, natOrdinal 3,
      wordGraph [], wordGraph [0], wordGraph s, y] ↔ y = natOrdinal (emptyExpression s) := by
  change ((wordGraph s = wordGraph [] ∧ y = natOrdinal 2) ∨
    (wordGraph s = wordGraph [0] ∧ y = natOrdinal 3) ∨
    (¬ wordGraph s = wordGraph [] ∧ ¬ wordGraph s = wordGraph [0] ∧ y = natOrdinal 0)) ↔ _
  simp only [wordGraph_injective.{u}.eq_iff, emptyExpression_apply]
  by_cases h0 : s = []
  · subst s
    simp
  · by_cases h1 : s = [0] <;> simp [h0, h1]

lemma emptyExpression_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ) :
    (emptyExpression.labelGraph : ZFSet.{u}) ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  have hF := finiteSequences_mem hM hinf hpair hunion hpower hsep
  have hs (s : List ℕ) := hM.mem_trans (mem_finiteSequences.mpr ⟨s, rfl⟩) hF
  let ps : Fin 5 → M := ![⟨natOrdinal 0, hn 0⟩, ⟨natOrdinal 2, hn 2⟩, ⟨natOrdinal 3, hn 3⟩,
    ⟨wordGraph [], hs []⟩, ⟨wordGraph [0], hs [0]⟩]
  apply bounded_labelGraph_mem hM hinf hpair hunion hpower hsep hrep emptyLabelPredicate ps emptyExpression
  intro s y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (wordGraph s)) y.val =
      ![natOrdinal 0, natOrdinal 2, natOrdinal 3, wordGraph [], wordGraph [0], wordGraph s, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_emptyLabelPredicate]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Re-rooting inside the model
-/
theorem nodeCode_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (c : BorelExpression) (hc : c.labelGraph ∈ M) (s : List ℕ) : (c.nodeCode s).labelGraph ∈ M := by
  unfold nodeCode
  split_ifs
  · exact emptyExpression_labelGraph_mem hM hinf hpair hunion hpower hsep hrep
  · exact below_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc s

lemma internalInterpretation_nodeCode (M : ZFSet.{u}) (c : BorelExpression) (hc : c.Valid)
    (b : ℕ → List ℕ) (hb : b 0 = []) (s : List ℕ) :
    internalInterpretation M (c.nodeCode s) (valid_nodeCode c hc s).2.2.2.2.2 b [] =
      internalInterpretation M c hc.2.2.2.2.2 b s := by
  have he := evaluate_nodeCode c hc (fun n => cyl (b n)) (by rw [hb]; exact cyl_nil) s
  simp only [internalInterpretation, he]

end PolishSpaceBook.BorelExpression
