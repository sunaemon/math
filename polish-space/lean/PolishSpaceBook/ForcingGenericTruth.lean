module

public import PolishSpaceBook.ForcingInternalTests

@[expose] public section

/-! # Truth and semantic forcing for every ground-model generic filter -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-- A generic filter meets every actual dense subset of P coded by an element of M. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    A filter $G$ is \termdefineas{M-generic}{$M$-generic} if it meets every dense set $D \IncludedIn P$ with $D \in M$.
-/
def ModelGeneric (P M : ZFSet.{u}) [Preorder (Condition P)] (G : Order.PFilter (Condition P)) : Prop :=
  ∀ D : ZFSet.{u}, D ∈ M → D ⊆ P → IsCoinitial {p : Condition P | p.val ∈ D} →
    ∃ p ∈ G, p.val ∈ D

lemma ModelGeneric.meets {P M : ZFSet.{u}} [Preorder (Condition P)]
    {G : Order.PFilter (Condition P)} (hG : ModelGeneric P M G) (A : Set (Condition P))
    (hA : conditionSet P A ∈ M) (hd : IsCoinitial A) : ∃ p ∈ G, p ∈ A := by
  have hsub : conditionSet P A ⊆ P := fun _ h => (ZFSet.mem_sep.mp h).1
  have hcode : {p : Condition P | p.val ∈ conditionSet P A} = A := by
    ext p
    exact mem_conditionSet P A p
  obtain ⟨p, hpG, hp⟩ := hG (conditionSet P A) hA hsub (by rw [hcode]; exact hd)
  exact ⟨p, hpG, (mem_conditionSet P A p).mp hp⟩

/-- The family is indexed externally by the ground model, not by its external power set. -/
def modelDenseSets (P M : ZFSet.{u}) [Preorder (Condition P)] : Set (Set (Condition P)) :=
  {A | ∃ D ∈ M, D ⊆ P ∧ A = {p : Condition P | p.val ∈ D} ∧ IsCoinitial A}

lemma modelDenseSets_countable (P M : ZFSet.{u}) [Preorder (Condition P)] (hc : M.toSet.Countable) :
    (modelDenseSets P M).Countable := by
  apply (hc.image (fun D => {p : Condition P | p.val ∈ D})).mono
  rintro A ⟨D, hD, _, rfl, _⟩
  exact ⟨D, hD, rfl⟩

/-- Countability gives a genuinely model-generic filter through each condition. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    If $M$ is externally countable, its actual dense subsets of $P$ form a countable family, because each is an element
    of $M$. Apply the descending-chain construction from §{sec:ground-models-forcing-notions} to this entire family,
    starting below any prescribed condition. The resulting filter is $M$-generic and contains that condition.
    This existence argument uses all ground-model dense sets, including ones unrelated to the displayed truth tests.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Rasiowa--Sikorski
-/
theorem exists_modelGeneric (P M : ZFSet.{u}) [Preorder (Condition P)]
    (hc : M.toSet.Countable) (p : Condition P) :
    ∃ G : Order.PFilter (Condition P), p ∈ G ∧ ModelGeneric P M G := by
  obtain ⟨G, hpG, hG⟩ := pfilter_meets_countable_dense (modelDenseSets P M)
    (modelDenseSets_countable P M hc) (by rintro A ⟨D, hD, hDP, he, hd⟩; exact hd) p
  refine ⟨G, hpG, ?_⟩
  intro D hD hDP hd
  exact hG _ ⟨D, hD, hDP, rfl, hd⟩

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
include hM hinf hpair hunion hpower hsep hrep hR

/-- All explicit tests in the rank and formula inductions are met by any model-generic filter. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Each of the four test sets is an actual dense subset of the condition set, as proved in §{sec:forcing-relation},
    and the preceding constructions put it in the model. Genericity therefore makes the filter meet all of them.
    The simultaneous rank induction proves atomic truth, and the induction on formulas proves implication and
    universal quantification using the other two tests. The valuation map from names onto the extension identifies
    quantification over names with quantification over its actual elements. These are exactly the hypotheses of the
    truth proof in §{sec:forcing-relation}, so it applies to this arbitrary generic filter.
    \end{proof}
-/
theorem modelGeneric_meets_tests (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    MeetsFormulaTests P.val M G := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro σ hσ _ τ hτ _
    exact hG.meets _ (membershipTest_mem hM hinf hpair hunion hpower hsep hrep P R hR ⟨σ, hσ⟩ ⟨τ, hτ⟩)
      (forcingDecision_dense _)
  · intro σ hσ _ τ hτ _
    exact hG.meets _ (equalityTest_mem hM hinf hpair hunion hpower hsep hrep P R hR ⟨σ, hσ⟩ ⟨τ, hτ⟩)
      (equalityTest_dense P.val σ τ)
  · intro n φ ψ xs
    exact hG.meets _ (implicationTest_mem hM hinf hpair hunion hpower hsep hrep P R hR φ ψ xs)
      (forcingImpTest_dense (force_lower P.val M φ xs) (force_saturated P.val M ψ xs))
  · intro n φ xs
    exact hG.meets _ (universalTest_mem hM hinf hpair hunion hpower hsep hrep P R hR φ xs)
      (forcingAllTest_dense (fun τ => force_saturated P.val M φ (Fin.snoc xs τ)))

/-- The truth lemma requires genericity, but not external countability of the model. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Truth for every generic filter
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The
    truth lemma connects conditions to truth in $M[G]$: every true statement in the extension is
    already forced by some condition in the generic filter.
-/
theorem modelGeneric_truth (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) :
    (∃ p ∈ G, p ∈ force P.val M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) :=
  formula_truth P.val M hM G (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG) φ xs

/-- For countable models the syntactic relation is exactly truth in all generic extensions through p. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Apply the saturation argument from the simultaneous induction in §{sec:forcing-relation}, now using the truth
    theorem for every $M$-generic filter. The preceding countability argument supplies a generic filter through
    any stronger condition needed in that argument. This gives both implications without another induction.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    At each step, once (‡) is known, (†) follows in both directions. The forward direction applies (‡) to
    every generic containing the condition. For the converse, if the condition does not syntactically force the
    formula, density-saturation gives a stronger condition below which no condition forces it. Take a generic
    through this stronger condition. If the formula held there, (‡) and directedness would yield a forcing condition
    below it, a contradiction. We use this argument whenever (†) is said to follow from (‡).
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Agreement with semantic forcing
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    By construction, $\forces$ is **monotone**: $p \forces \varphi$ and $q \le p$ imply $q \forces \varphi$.
-/
theorem force_iff_all_modelGeneric (hc : M.toSet.Countable) {n : ℕ}
    (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) (p : Condition P.val) :
    p ∈ force P.val M φ xs ↔ ∀ G : Order.PFilter (Condition P.val), ModelGeneric P.val M G → p ∈ G →
      φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) := by
  classical
  constructor
  · intro hp G hG hpG
    exact (modelGeneric_truth hM hinf hpair hunion hpower hsep hrep P R hR G hG φ xs).mp ⟨p, hpG, hp⟩
  · intro h
    by_contra hp
    obtain ⟨q, hqp, hq⟩ := not_forcing_refinement (force_saturated P.val M φ xs) hp
    obtain ⟨G, hqG, hG⟩ := exists_modelGeneric P.val M hc q
    have ht := h G hG (G.mem_of_le hqp hqG)
    obtain ⟨r, hrG, hr⟩ := (modelGeneric_truth hM hinf hpair hunion hpower hsep hrep P R hR G hG φ xs).mpr ht
    exact pfilter_not_pos_neg G (force_lower P.val M φ xs) hrG hqG hr hq

/-- The dense forcing set belongs to M by the actual defining formula, so
genericity meets it and the truth lemma applies. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For Polish-space applications, the main working principle is: to show that every generic extension satisfies a statement
    about a named Polish-space object, it suffices to show that every condition has a stronger condition forcing that
    statement. This is the forcing form of a dense-set argument.
-/
theorem modelGeneric_truth_of_dense_forcing (G : Order.PFilter (Condition P.val))
    (hG : ModelGeneric P.val M G) {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name P.val M)
    (hd : ∀ p : Condition P.val, ∃ q : Condition P.val, q ≤ p ∧ q ∈ force P.val M φ xs) :
    φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) := by
  have hset := forcingSet_mem hM hinf hpair hunion hpower hsep hrep P R hR φ xs
  have hsub : forcingSet P.val M φ xs ⊆ P.val := fun _ h => (ZFSet.mem_sep.mp h).1
  have hcoin : IsCoinitial {p : Condition P.val | p.val ∈ forcingSet P.val M φ xs} := by
    intro p
    obtain ⟨q, hqp, hq⟩ := hd p
    exact ⟨q, (mem_forcingSet P.val M φ xs q).mpr hq, hqp⟩
  obtain ⟨p, hpG, hp⟩ := hG _ hset hsub hcoin
  exact (modelGeneric_truth hM hinf hpair hunion hpower hsep hrep P R hR G hG φ xs).mp
    ⟨p, hpG, (mem_forcingSet P.val M φ xs p).mp hp⟩

/-- The working principle with semantic forcing uses countability only to
identify semantic forcing with the recursively defined forcing set. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *To show that every generic extension satisfies a statement about a named Polish-space object, it suffices to show that
    every condition has a stronger condition forcing that statement.*
-/
theorem modelGeneric_truth_of_dense_semantic_forcing (hc : M.toSet.Countable)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) {n : ℕ}
    (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M)
    (hd : ∀ p : Condition P.val, ∃ q : Condition P.val, q ≤ p ∧
      ∀ H : Order.PFilter (Condition P.val), ModelGeneric P.val M H → q ∈ H →
        φ.Realize Empty.elim (fun i => evalName P.val M H (xs i))) :
    φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) := by
  apply modelGeneric_truth_of_dense_forcing hM hinf hpair hunion hpower hsep hrep P R hR G hG φ xs
  intro p
  obtain ⟨q, hqp, hq⟩ := hd p
  exact ⟨q, hqp, (force_iff_all_modelGeneric hM hinf hpair hunion hpower hsep hrep P R hR hc φ xs q).mpr hq⟩

/-- The truth lemma expressed with semantic forcing, as in the main forcing theorem. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: forcing theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    (‡) is the
    \termuseas{forcing truth lemma}{truth lemma}: every formula true in $M[G]$ is forced by some condition in $G$, and every
    formula forced by a condition in $G$ holds in $M[G]$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Distinguish the \emph{semantic} forcing relation $p \forces \varphi$, defined externally by
    quantifying over $M$-generic filters, from the \emph{syntactic} relation $p \forces^* \varphi$ given by the
    atomic recursion and formula clauses below. The construction in §{sec:internal-atomic-forcing} defines the
    atomic relations inside $M$. The construction in §{sec:internal-forcing-formulas} defines the names internally
    and extends the definition through each fixed formula. Thus $\forces^*$ is $M$-definable.
    The internal test sets constructed in §{sec:internal-generic-truth} allow the truth proof below to apply to
    every $M$-generic filter. The equivalence
    $p \forces^* \varphi \Leftrightarrow p \forces \varphi$ transfers this definition to the semantic relation,
    and the same induction gives the truth lemma.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    (†) $p \forces^* \varphi(\vec\tau) \;\Longleftrightarrow\; p \forces \varphi(\vec\tau)$,
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    (‡) For every $M$-generic $G$,
    $M[G] \models \varphi(\vec\tau^G) \;\Longleftrightarrow\; \exists p \in G\;(p \forces^* \varphi(\vec\tau)).$
-/
theorem modelGeneric_semantic_truth (hc : M.toSet.Countable)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) :
    φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) ↔
      ∃ p ∈ G, ∀ H : Order.PFilter (Condition P.val), ModelGeneric P.val M H → p ∈ H →
        φ.Realize Empty.elim (fun i => evalName P.val M H (xs i)) := by
  rw [← modelGeneric_truth hM hinf hpair hunion hpower hsep hrep P R hR G hG φ xs]
  apply exists_congr
  intro p
  exact and_congr_right (fun _ =>
    force_iff_all_modelGeneric hM hinf hpair hunion hpower hsep hrep P R hR hc φ xs p)

/-- The constructed first-order formula defines semantic forcing as well as its recursive presentation. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The construction in §{sec:internal-forcing-formulas} therefore gives, for each fixed formula,
    a formula $\rho_\varphi(P,R,p,\vec\tau)$ that defines semantic forcing inside the model.
    The proof separates internal definability, truth for an existing generic filter, and the countability assumption
    that guarantees enough generic filters to characterize semantic forcing.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: forcing theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    This completes both inductions. (†) is the \termuse{definability} half of the forcing theorem: for each fixed
    $\varphi$, the syntactic relation $\forces^*$ is $M$-definable from $P$, and equals the semantic relation
    $\forces$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the following semantic definition, assume that $M$ is countable in the ambient universe, so that
    a generic filter through each condition exists. The semantic definition is:
    $$p \forces \varphi(\tau_0,\ldots,\tau_{k-1})$$
    iff for every $M$-generic $G \IncludedIn P$ with $p \in G$,
    $$M[G] \models \varphi(\tau_0^G,\ldots,\tau_{k-1}^G).$$
    This definition uses generic filters outside $M$. The \termuse{forcing theorem} says that this external-looking relation
    is actually definable in $M$ and satisfies the expected truth lemma.
-/
theorem semantic_forcing_definable (hc : M.toSet.Countable) {n : ℕ}
    (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) (p : Condition P.val) :
    (forcingTranslation φ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) P R ⟨p.val, hM.mem_trans p.property P.property⟩) ↔
      ∀ G : Order.PFilter (Condition P.val), ModelGeneric P.val M G → p ∈ G →
        φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) :=
  (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ xs p).trans
    (force_iff_all_modelGeneric hM hinf hpair hunion hpower hsep hrep P R hR hc φ xs p)

end Model
end PolishSpaceBook.SetTheoryModels
