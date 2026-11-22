module

public import PolishSpaceBook.ForcingFormulas

@[expose] public section

/-! # The truth lemma for arbitrary first-order membership formulas

The interpretation uses mathlib's `BoundedFormula.Realize` on the actual
extension, not a second bespoke satisfaction predicate. Explicit dense tests
are kept separate here; `ForcingInternalTests` gives their ground-model codes,
and `ForcingGenericTruth` derives these hypotheses from ordinary genericity.
-/

noncomputable section
namespace PolishSpaceBook.ForcingFormulas
open FirstOrder Language ZFSet ForcingNames ForcingAtomic
universe u
variable (P M : ZFSet.{u}) [Preorder (Condition P)]

structure MeetsFormulaTests (G : Order.PFilter (Condition P)) : Prop where
  atoms : MeetsAtomicTests P M G
  implication : ∀ {n} (φ ψ : Formula n) (xs : Fin n → Name P M),
    ∃ p ∈ G, p ∈ forcingImpTest (force P M φ xs) (force P M ψ xs)
  universal : ∀ {n} (φ : Formula (n + 1)) (xs : Fin n → Name P M),
    ∃ p ∈ G, p ∈ forcingAllTest (fun τ => force P M φ (Fin.snoc xs τ))

/-- Negation needs no test beyond the implication test with false consequent. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The decision tests used for negation and existential quantification already follow from the primitive tests.
    The implication test for $\varphi\to\bot$ is exactly the decision test for $\varphi$.
-/
lemma MeetsFormulaTests.decision {G : Order.PFilter (Condition P)}
    (hG : MeetsFormulaTests P M G) {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) :
    ∃ p ∈ G, p ∈ forcingDecision (force P M φ xs) := by
  obtain ⟨p, hpG, hp | ⟨hp, _⟩⟩ := hG.implication φ .falsum xs
  · exact ⟨p, hpG, Or.inr hp⟩
  · exact ⟨p, hpG, Or.inl hp⟩

/-- The universal test for the negated matrix decides its existential witness set. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For the existential step, put $C_\tau:=\{p:p\forces^*\varphi(\tau)\}$ and apply the universal test to
    $\neg\varphi$. Its first alternative says that no strengthening belongs to any $C_\tau$.
    Its second supplies a name $\tau$ and a condition forcing $\neg\neg\varphi(\tau)$.
    Such a condition forces $\varphi(\tau)$: otherwise the refinement rule would give a strengthening forcing
    $\neg\varphi(\tau)$, contradicting double negation. Conversely, monotonicity excludes a negative strengthening
    of a condition forcing $\varphi(\tau)$. Thus this universal test is precisely the decision test for
    $\bigcup_{\tau\in M^P}C_\tau$, with its two alternatives interchanged.
-/
lemma MeetsFormulaTests.existsDecision {G : Order.PFilter (Condition P)}
    (hG : MeetsFormulaTests P M G) {n : ℕ} (φ : Formula (n + 1))
    (xs : Fin n → Name P M) :
    ∃ p ∈ G, p ∈ forcingDecision (⋃ τ, force P M φ (Fin.snoc xs τ)) := by
  obtain ⟨p, hpG, hp | hp⟩ := hG.universal φ.not xs
  · refine ⟨p, hpG, Or.inr ?_⟩
    intro q hqp hq
    obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hq
    exact hp τ q hqp hτ
  · obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hp
    change p ∈ forcingNeg (forcingNeg (force P M φ (Fin.snoc xs τ))) at hτ
    rw [forcingNeg_neg_eq (force_lower P M φ (Fin.snoc xs τ))
      (force_saturated P M φ (Fin.snoc xs τ))] at hτ
    exact ⟨p, hpG, Or.inl (Set.mem_iUnion.mpr ⟨τ, hτ⟩)⟩

/-- The direct conjunction step uses a common strengthening, as in the text. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Conjunction.} If the conjunction is true in $M[G]$, induction gives conditions $p,q\in G$
    forcing its two conjuncts. Choose $r\in G$ with $r\le p,q$. Monotonicity and the conjunction clause
    show that $r$ forces the conjunction. Conversely, a condition forcing the conjunction forces each conjunct,
    so induction makes both true in the extension. This proves (‡), and (†) follows by the general argument.
-/
lemma formula_and_truth_step (G : Order.PFilter (Condition P)) {n : ℕ}
    (φ ψ : Formula n) (xs : Fin n → Name P M)
    (hφ : (∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)))
    (hψ : (∃ p ∈ G, p ∈ force P M ψ xs) ↔
      ψ.Realize Empty.elim (fun i => evalName P M G (xs i))) :
    (∃ p ∈ G, p ∈ force P M (φ ⊓ ψ) xs) ↔
      (φ ⊓ ψ).Realize Empty.elim (fun i => evalName P M G (xs i)) := by
  rw [force_and, forcingAnd_truth G (force_lower P M φ xs) (force_lower P M ψ xs),
    hφ, hψ, BoundedFormula.realize_inf]

/-- The negative decision is obtained from the primitive implication test. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Negation.} By induction, $\varphi$ is false in $M[G]$ exactly when no condition in $G$ forces it.
    Meet the dense decision set
    $$D:=\{q:q\forces^*\varphi\}\cup\{q:q\forces^*\neg\varphi\}.$$
    If $\varphi$ is false, the first alternative is impossible, so some condition in $G$ forces its negation.
    Conversely, suppose $p\in G$ forces $\neg\varphi$. If $\varphi$ were true, induction would supply
    $q\in G$ forcing $\varphi$. A common strengthening $r\in G$ of $p,q$ would force $\varphi$ by monotonicity,
    contrary to the negation clause at $p$. This proves (‡), and hence (†), for negation.
-/
lemma formula_not_truth_step (G : Order.PFilter (Condition P))
    (hG : MeetsFormulaTests P M G) {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M)
    (hφ : (∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i))) :
    (∃ p ∈ G, p ∈ force P M φ.not xs) ↔
      φ.not.Realize Empty.elim (fun i => evalName P M G (xs i)) := by
  rw [force_not, forcingNeg_truth G (force_lower P M φ xs) (hG.decision P M φ xs),
    hφ, BoundedFormula.realize_not]

/-- The existential step extracts a name and then evaluates it in the actual extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Existential.} If $M[G]\models\exists x\,\varphi(x)$, choose a witness.
    By the definition of the extension, it is $\tau^G$ for some $\tau\in M^P$.
    Induction supplies $q\in G$ forcing $\varphi(\tau)$. Every strengthening of $q$ is therefore an existential witness
    condition, so $q$ forces the existential formula.
    Conversely, if $p\in G$ forces the existential formula, its witness conditions are dense below $p$.
    Meet their decision test, just as in the membership case, to obtain $q\in G$ and a name $\tau$ with
    $q\forces^*\varphi(\tau)$. Induction gives the witness $\tau^G$ in the extension.
-/
lemma formula_exists_truth_step (G : Order.PFilter (Condition P))
    (hG : MeetsFormulaTests P M G) {n : ℕ} (φ : Formula (n + 1))
    (xs : Fin n → Name P M)
    (ih : ∀ τ : Name P M, (∃ p ∈ G, p ∈ force P M φ (Fin.snoc xs τ)) ↔
      φ.Realize Empty.elim (evalName P M G ∘ Fin.snoc xs τ)) :
    (∃ p ∈ G, p ∈ force P M φ.ex xs) ↔
      φ.ex.Realize Empty.elim (fun i => evalName P M G (xs i)) := by
  rw [force_exists, forcingExists_truth G
    (fun τ => force_lower P M φ (Fin.snoc xs τ)) (hG.existsDecision P M φ xs),
    BoundedFormula.realize_ex]
  have hv (τ : Name P M) :
      (∃ p ∈ G, p ∈ force P M φ (Fin.snoc xs τ)) ↔
      φ.Realize Empty.elim (Fin.snoc (fun i => evalName P M G (xs i)) (evalName P M G τ)) := by
    have he := Fin.comp_snoc (evalName P M G) xs τ
    simp only [Function.comp_def] at he
    rw [← he]
    exact ih τ
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨evalName P M G τ, (hv τ).mp hτ⟩
  · rintro ⟨x, hx⟩
    obtain ⟨τ, rfl⟩ := evalName_surjective P M G x
    exact ⟨τ, (hv τ).mpr hx⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    If $p\in G$ forces the universal formula, it forces every name instance.
    Every element of $M[G]$ is the valuation of a name in $M$, so induction makes the universal formula true in the
    actual domain of the extension. Conversely, suppose every element satisfies the formula and meet the displayed test.
    A condition in its second part would rule out every forcing condition for one name instance.
    That instance is true by assumption, so induction and directedness give a contradiction.
    Hence a condition in $G$ lies in the first part and forces the universal formula.
    This proves (‡), including the passage between quantification over names and quantification over elements of $M[G]$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The atomic cases are handled first by an inner induction on the rank-pair $\prec$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    If a condition in $G$ forces the implication and the antecedent is true, the induction hypothesis gives a condition
    in $G$ forcing the antecedent. A common strengthening forces the consequent, so it is true by induction.
    Conversely, suppose the implication is true in $M[G]$ and meet the displayed test.
    Its second part would force the antecedent to be true and would prevent any condition in the filter from forcing
    the consequent, contradicting induction and directedness. Hence the filter meets the first part.
    This proves both directions of (‡) for implication.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    We make the dense tests used in that induction explicit.
-/
theorem formula_truth (hM : M.IsTransitive) (G : Order.PFilter (Condition P))
    (hG : MeetsFormulaTests P M G) {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) :
    (∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)) := by
  induction φ with
  | falsum => simp [force, BoundedFormula.Realize]
  | equal s t =>
    rw [BoundedFormula.Realize, term_realize, term_realize, Subtype.ext_iff]
    exact atomic_truth P M hM G hG.atoms true _ _
      (termName P M s xs).property.1 (termName P M t xs).property.1
      (termName P M s xs).property.2 (termName P M t xs).property.2
  | rel R ts =>
    cases R
    simp only [BoundedFormula.Realize, term_realize]
    exact atomic_truth P M hM G hG.atoms false _ _
      (termName P M (ts 0) xs).property.1 (termName P M (ts 1) xs).property.1
      (termName P M (ts 0) xs).property.2 (termName P M (ts 1) xs).property.2
  | imp φ ψ ihφ ihψ =>
    exact forcingImp_truth G (force_lower P M φ xs) (force_lower P M ψ xs)
      (ihφ xs).symm (ihψ xs).symm (hG.implication φ ψ xs)
  | all φ ih =>
    have hv (τ : Name P M) :
        φ.Realize Empty.elim (Fin.snoc (fun i => evalName P M G (xs i)) (evalName P M G τ)) ↔
        ∃ p ∈ G, p ∈ force P M φ (Fin.snoc xs τ) := by
      have he : evalName P M G ∘ Fin.snoc xs τ =
          Fin.snoc (evalName P M G ∘ xs) (evalName P M G τ) :=
        Fin.comp_snoc (evalName P M G) xs τ
      simp only [Function.comp_def] at he
      rw [← he]
      exact (ih (Fin.snoc xs τ)).symm
    have ht := forcingAll_truth G (fun τ => force_lower P M φ (Fin.snoc xs τ)) hv (hG.universal φ xs)
    constructor
    · intro h x
      obtain ⟨τ, rfl⟩ := evalName_surjective P M G x
      exact ht.mp h τ
    · intro h
      exact ht.mpr (fun τ => h (evalName P M G τ))

instance : Countable membershipLanguage.Symbols := by
  unfold Language.Symbols
  infer_instance

instance (n : ℕ) : Countable (Formula n) :=
  Function.Injective.countable (f := fun φ => (⟨n, φ⟩ : Σ n, Formula n)) sigma_mk_injective

abbrev ImplicationInput := Σ n : ℕ, (Formula n × Formula n) × (Fin n → Name P M)
abbrev UniversalInput := Σ n : ℕ, Formula (n + 1) × (Fin n → Name P M)

def implicationTest (i : ImplicationInput P M) : Set (Condition P) :=
  forcingImpTest (force P M i.2.1.1 i.2.2) (force P M i.2.1.2 i.2.2)

def universalTest (i : UniversalInput P M) : Set (Condition P) :=
  forcingAllTest (fun τ => force P M i.2.1 (Fin.snoc i.2.2 τ))

def formulaTests : Set (Set (Condition P)) :=
  atomicTests P M ∪ Set.range (implicationTest P M) ∪ Set.range (universalTest P M)

lemma formulaTests_countable (hc : M.toSet.Countable) : (formulaTests P M).Countable := by
  have hn : ({σ : ZFSet.{u} | σ ∈ M ∧ IsName P σ} : Set ZFSet.{u}).Countable :=
    hc.mono (fun _ h => h.1)
  let : Countable (Name P M) := hn.to_subtype
  exact ((atomicTests_countable P M hc).union (Set.countable_range _)).union (Set.countable_range _)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Their density was proved in §{sec:forcing-relation}.
    \end{proof}
-/
lemma formulaTests_dense : ∀ D ∈ formulaTests P M, IsCoinitial D := by
  intro D hD
  rcases hD with (hD | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact atomicTests_dense P M D hD
  · exact forcingImpTest_dense (force_lower P M i.2.1.1 i.2.2) (force_saturated P M i.2.1.2 i.2.2)
  · exact forcingAllTest_dense (fun τ => force_saturated P M i.2.1 (Fin.snoc i.2.2 τ))

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The entire argument can be run with an explicit countable family of tests.
    There are countably many finite formulas and, when $M$ is countable, countably many finite tuples of names in $M$.
    Take the atomic tests and the implication and universal tests for every such formula and tuple.
    The descending-chain construction meets this whole family through any prescribed condition.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For $M$-generic filters, each individual test belongs to $M$ by definability for its fixed formula and parameters.
    No single internal truth definition for all formula codes is required.
-/
/-- Enumerating the formulas and finite name assignments makes all tests countable. -/
theorem exists_formula_test_filter (hc : M.toSet.Countable) (p : Condition P) :
    ∃ G : Order.PFilter (Condition P), p ∈ G ∧ MeetsFormulaTests P M G := by
  obtain ⟨G, hpG, hG⟩ := pfilter_meets_countable_dense (formulaTests P M)
    (formulaTests_countable P M hc) (formulaTests_dense P M) p
  refine ⟨G, hpG, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro σ hσ hσn τ hτ hτn
    exact hG _ (Or.inl (Or.inl (Or.inl ⟨(σ, τ), ⟨⟨hσ, hσn⟩, ⟨hτ, hτn⟩⟩, rfl⟩)))
  · intro σ hσ hσn τ hτ hτn
    exact hG _ (Or.inl (Or.inl (Or.inr ⟨(σ, τ), ⟨⟨hσ, hσn⟩, ⟨hτ, hτn⟩⟩, rfl⟩)))
  · intro n φ ψ xs
    exact hG _ (Or.inl (Or.inr ⟨⟨n, (φ, ψ), xs⟩, rfl⟩))
  · intro n φ xs
    exact hG _ (Or.inr ⟨⟨n, φ, xs⟩, rfl⟩)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The verified definitions of the other connectives reduce their truth to the primitive induction.
    It therefore gives truth for every formula in these extensions, and the same saturation argument
    identifies forcing with truth in all such extensions containing the condition.
-/
/-- The syntactic forcing clause agrees with truth in every explicit test extension. -/
theorem force_iff_all_test_filters (hM : M.IsTransitive) (hc : M.toSet.Countable)
    {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) (p : Condition P) :
    p ∈ force P M φ xs ↔ ∀ G : Order.PFilter (Condition P), MeetsFormulaTests P M G → p ∈ G →
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)) := by
  classical
  constructor
  · intro hp G hG hpG
    exact (formula_truth P M hM G hG φ xs).mp ⟨p, hpG, hp⟩
  · intro hs
    by_contra hp
    obtain ⟨q, hqp, hq⟩ := not_forcing_refinement (force_saturated P M φ xs) hp
    obtain ⟨G, hqG, hG⟩ := exists_formula_test_filter P M hc q
    have hv := hs G hG (G.mem_of_le hqp hqG)
    obtain ⟨r, hrG, hr⟩ := (formula_truth P M hM G hG φ xs).mpr hv
    exact pfilter_not_pos_neg G (force_lower P M φ xs) hrG hqG hr hq

end PolishSpaceBook.ForcingFormulas
