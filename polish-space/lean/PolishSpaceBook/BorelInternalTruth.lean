module

public import PolishSpaceBook.BorelExpressionEvaluation
public import PolishSpaceBook.SetTheoryInternalBooleanEvaluation

@[expose] public section

/-! # Comparing internal Boolean evaluations with Borel expression semantics

The set parameters explicitly encode the word domain, child relation, labels,
and leaf tests at a fixed point. These hypotheses concern representation of the
input, not existence or correctness of an internal evaluation.
-/

noncomputable section
namespace PolishSpaceBook
open ZFSet SetTheoryModels SetTheoryModels.BooleanEvaluation
open scoped Classical
universe u

namespace BorelExpression

/-- The true nodes of the actual external evaluation, represented by sets. -/
def codedTruth {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (V : ℕ → Set X) (x : X) {T : ZFSet.{u}} (e : List ℕ ≃ T) : ZFSet.{u} :=
  T.sep (fun t => ∃ s, (e s).val = t ∧ x ∈ c.evaluate hw V s)

lemma mem_codedTruth {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (V : ℕ → Set X) (x : X) {T : ZFSet.{u}} (e : List ℕ ≃ T) (s : List ℕ) :
    (e s).val ∈ c.codedTruth hw V x e ↔ x ∈ c.evaluate hw V s := by
  rw [codedTruth, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, t, ht, hx⟩
    have he : t = s := e.injective (Subtype.ext ht)
    exact he ▸ hx
  · exact fun hx => ⟨(e s).property, s, rfl, hx⟩

/-- Each recursive semantic clause is exactly the bounded Boolean clause. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Let $E$ be the set of $e(s)$ such that $x$ belongs to the external set assigned to $s$.
    At a union node, this holds exactly when it holds at some present child. At a complement node, it holds
    exactly when it fails at the unique child. At a leaf, the condition is precisely $e(s)\in L$; absent nodes
    are false. Thus $\sigma(T,E)$ holds.
-/
theorem codedTruth_partial {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (V : ℕ → Set X) (x : X) {T R U C L : ZFSet.{u}} (e : List ℕ ≃ T)
    (hR : ∀ t s, pair (e t).val (e s).val ∈ R ↔ c.Child t s)
    (hU : ∀ s, (e s).val ∈ U ↔ c s = 1)
    (hC : ∀ s, (e s).val ∈ C ↔ c s = 2)
    (hL : ∀ s, (e s).val ∈ L ↔ 3 ≤ c s ∧ x ∈ V (c s - 3)) :
    Partial T R U C L T (c.codedTruth hw V x e) := by
  refine ⟨fun _ h => h, fun _ h => (ZFSet.mem_sep.mp h).1, fun _ _ _ ht _ => ht, ?_⟩
  intro a ha
  obtain ⟨s, hs⟩ := e.surjective ⟨a, ha⟩
  have hsa : (e s).val = a := congrArg Subtype.val hs
  rw [← hsa, mem_codedTruth, c.evaluate_isEvaluation hw V s]
  have hchildren (hn : c s ≠ 0) :
      (∃ t ∈ T, pair t (e s).val ∈ R ∧ t ∈ c.codedTruth hw V x e) ↔
        ∃ k, c (s ++ [k]) ≠ 0 ∧ x ∈ c.evaluate hw V (s ++ [k]) := by
    constructor
    · rintro ⟨t, ht, hr, he⟩
      obtain ⟨w, hw'⟩ := e.surjective ⟨t, ht⟩
      have hwt : (e w).val = t := congrArg Subtype.val hw'
      rw [← hwt, hR] at hr
      obtain ⟨_, k, rfl, hk⟩ := hr
      rw [← hwt, mem_codedTruth] at he
      exact ⟨k, hk, he⟩
    · rintro ⟨k, hk, hx⟩
      exact ⟨(e (s ++ [k])).val, (e (s ++ [k])).property,
        (hR _ _).mpr ⟨hn, k, rfl, hk⟩, (mem_codedTruth c hw V x e _).mpr hx⟩
  unfold Step
  rw [hU, hC, hL]
  by_cases h0 : c s = 0
  · simp [h0]
  · rw [hchildren h0]
    by_cases h1 : c s = 1
    · simp [h1]
    · by_cases h2 : c s = 2
      · simp [h2]
      · have h3 : 3 ≤ c s := by omega
        simp [h0, h1, h2, h3]

/-- Internal closure produces exactly the externally evaluated truth set. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The bijection transports well-foundedness of the child relation to $R$.
    The theorem puts this very set $E$ in $M$,
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a fixed point, evaluating a Borel code amounts to marking its true nodes. We construct this set of nodes
    inside a transitive model before comparing it with the external evaluation of §{sec:borel-codes}.
-/
theorem codedTruth_mem {X : Type*} {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (V : ℕ → Set X) (x : X)
    (T R U C L : M) (e : List ℕ ≃ T.val)
    (hR : ∀ t s, pair (e t).val (e s).val ∈ R.val ↔ c.Child t s)
    (hU : ∀ s, (e s).val ∈ U.val ↔ c s = 1)
    (hC : ∀ s, (e s).val ∈ C.val ↔ c s = 2)
    (hL : ∀ s, (e s).val ∈ L.val ↔ 3 ≤ c s ∧ x ∈ V (c s - 3)) :
    c.codedTruth hw V x e ∈ M := by
  have hwell : WellFounded (fun t s : T.val => pair t.val s.val ∈ R.val) := by
    have hi := InvImage.wf e.symm hw
    apply hi.mono
    intro t s hts
    exact (hR (e.symm t) (e.symm s)).mp (by simpa using hts)
  exact external_evaluation_mem hM hpair hunion hsep T R U C L hwell
    (c.codedTruth_partial hw V x e hR hU hC hL)

/-- The first-order truth formula agrees with Borel membership at every word. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    and the truth-formula equivalence proves the assertion at every
    node, including the root.
-/
theorem realize_codedTruth {X : Type*} {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (V : ℕ → Set X) (x : X)
    (T R U C L : M) (e : List ℕ ≃ T.val)
    (hR : ∀ t s, pair (e t).val (e s).val ∈ R.val ↔ c.Child t s)
    (hU : ∀ s, (e s).val ∈ U.val ↔ c s = 1)
    (hC : ∀ s, (e s).val ∈ C.val ↔ c s = 2)
    (hL : ∀ s, (e s).val ∈ L.val ↔ 3 ≤ c s ∧ x ∈ V (c s - 3)) (s : List ℕ) :
    truthFormula.Realize Empty.elim
      ![T, R, U, C, L, ⟨(e s).val, hM.mem_trans (e s).property T.property⟩] ↔
        x ∈ c.evaluate hw V s := by
  have hwell : WellFounded (fun t s : T.val => pair t.val s.val ∈ R.val) := by
    apply (InvImage.wf e.symm hw).mono
    intro t s hts
    exact (hR (e.symm t) (e.symm s)).mp (by simpa using hts)
  exact (realize_truthFormula_external hM hpair hunion hsep T R U C L _ hwell
    (c.codedTruth_partial hw V x e hR hU hC hL)).trans (c.mem_codedTruth hw V x e s)

/-- Both conclusions of the comparison corollary, with the same input presentation. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Comparison with Borel-code evaluation
-/
theorem codedTruth_mem_and_realize {X : Type*} {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (V : ℕ → Set X) (x : X)
    (T R U C L : M) (e : List ℕ ≃ T.val)
    (hR : ∀ t s, pair (e t).val (e s).val ∈ R.val ↔ c.Child t s)
    (hU : ∀ s, (e s).val ∈ U.val ↔ c s = 1)
    (hC : ∀ s, (e s).val ∈ C.val ↔ c s = 2)
    (hL : ∀ s, (e s).val ∈ L.val ↔ 3 ≤ c s ∧ x ∈ V (c s - 3)) :
    c.codedTruth hw V x e ∈ M ∧ ∀ s : List ℕ,
    (truthFormula.Realize Empty.elim
      ![T, R, U, C, L, ⟨(e s).val, hM.mem_trans (e s).property T.property⟩] ↔
        x ∈ c.evaluate hw V s) := by
  exact ⟨c.codedTruth_mem hM hpair hunion hsep hw V x T R U C L e hR hU hC hL,
    fun s => c.realize_codedTruth hM hpair hunion hsep hw V x T R U C L e hR hU hC hL s⟩

end BorelExpression
end PolishSpaceBook
