module

public import PolishSpaceBook.ForcingGenericTruth
public import PolishSpaceBook.ForcingDisjunctionTruth

@[expose] public section

/-! # Simultaneous truth and semantic equivalence

At each atomic rank and each formula stage, first establish truth and then
obtain semantic equivalence by saturation and a generic through every condition.
The recursive hypotheses contain both conclusions, although the truth steps
need only their truth components.
-/
noncomputable section
namespace PolishSpaceBook.ForcingFormulas
open FirstOrder Language ZFSet ForcingNames ForcingAtomic
universe u
variable (P M : ZFSet.{u}) [Preorder (Condition P)]

/-- The common argument from truth to semantic equivalence, reused at every stage. -/
theorem semantics_of_truth (Good : Order.PFilter (Condition P) → Prop)
    (hexists : ∀ p : Condition P, ∃ G, Good G ∧ p ∈ G)
    (A : Set (Condition P)) (hA : IsLowerSet A) (hsA : forcingDense A ⊆ A)
    (V : Order.PFilter (Condition P) → Prop)
    (ht : ∀ G, Good G → ((∃ p ∈ G, p ∈ A) ↔ V G)) (p : Condition P) :
    p ∈ A ↔ ∀ G, Good G → p ∈ G → V G := by
  classical
  constructor
  · intro hp G hG hpG
    exact (ht G hG).mp ⟨p, hpG, hp⟩
  · intro hv
    by_contra hp
    obtain ⟨q, hqp, hq⟩ := not_forcing_refinement hsA hp
    obtain ⟨G, hG, hqG⟩ := hexists q
    have hVG := hv G hG (G.mem_of_le hqp hqG)
    obtain ⟨r, hrG, hr⟩ := (ht G hG).mpr hVG
    exact pfilter_not_pos_neg G hA hrG hqG hr hq

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
/-- The atomic rank-pair induction carries truth and semantic equivalence together. -/
theorem atomic_truth_semantics
    (Good : Order.PFilter (Condition P) → Prop)
    (htests : ∀ G, Good G → MeetsFormulaTests P M G)
    (hexists : ∀ p : Condition P, ∃ G, Good G ∧ p ∈ G)
    (hM : M.IsTransitive) (b : Bool) (σ τ : ZFSet.{u})
    (hσ : σ ∈ M) (hτ : τ ∈ M) (hσn : IsName P σ) (hτn : IsName P τ) :
    (∀ G, Good G → ((∃ p ∈ G, p ∈ atomic P b σ τ) ↔
      if b then value P G σ = value P G τ else value P G σ ∈ value P G τ)) ∧
    (∀ p : Condition P, p ∈ atomic P b σ τ ↔ ∀ G, Good G → p ∈ G →
      if b then value P G σ = value P G τ else value P G σ ∈ value P G τ) := by
  have ht : ∀ G, Good G → ((∃ p ∈ G, p ∈ atomic P b σ τ) ↔
      if b then value P G σ = value P G τ else value P G σ ∈ value P G τ) := by
    intro G hgood
    have hG := (htests G hgood).atoms
    cases b
    · change (∃ p ∈ G, p ∈ atomic P false σ τ) ↔ value P G σ ∈ value P G τ
      constructor
      · rintro ⟨p, hpG, hp⟩
        rw [membership_eq] at hp
        obtain ⟨q, hqG, π, r, hπ, hqr, hq⟩ :=
          pfilter_dense_witness G hpG hp (hG.membership σ hσ hσn τ hτ hτn)
        have he := ((atomic_truth_semantics Good htests hexists hM true σ π hσ (child_mem_ground hM hτ hπ) hσn (hτn.child hπ)).1 G hgood).mp ⟨q, hqG, hq⟩
        exact (mem_value P G τ _).mpr ⟨π, r, G.mem_of_le hqr hqG, hπ, he.symm⟩
      · intro h
        obtain ⟨π, r, hrG, hπ, he⟩ := (mem_value P G τ _).mp h
        obtain ⟨q, hqG, hq⟩ :=
          ((atomic_truth_semantics Good htests hexists hM true σ π hσ (child_mem_ground hM hτ hπ) hσn (hτn.child hπ)).1 G hgood).mpr he.symm
        obtain ⟨p, hpG, hpq, hpr⟩ := G.directed q hqG r hrG
        exact ⟨p, hpG, membership_of_witness P
          ⟨π, r, hπ, hpr, atomic_lower P true σ π hpq hq⟩⟩
    · change (∃ p ∈ G, p ∈ atomic P true σ τ) ↔ value P G σ = value P G τ
      constructor
      · rintro ⟨p, hpG, hp⟩
        apply ZFSet.ext
        intro x
        constructor
        · intro hx
          obtain ⟨π, r, hrG, hπ, he⟩ := (mem_value P G σ x).mp hx
          obtain ⟨q, hqG, hqp, hqr⟩ := G.directed p hpG r hrG
          have hq := equality_member P (atomic_lower P true σ τ hqp hp) hπ hqr
          have hv := ((atomic_truth_semantics Good htests hexists hM false π τ (child_mem_ground hM hσ hπ) hτ (hσn.child hπ) hτn).1 G hgood).mp ⟨q, hqG, hq⟩
          exact he ▸ hv
        · intro hx
          obtain ⟨π, r, hrG, hπ, he⟩ := (mem_value P G τ x).mp hx
          obtain ⟨q, hqG, hqp, hqr⟩ := G.directed p hpG r hrG
          have hq := equality_member P (equality_symm P σ τ (atomic_lower P true σ τ hqp hp)) hπ hqr
          have hv := ((atomic_truth_semantics Good htests hexists hM false π σ (child_mem_ground hM hτ hπ) hσ (hτn.child hπ) hσn).1 G hgood).mp ⟨q, hqG, hq⟩
          exact he ▸ hv
      · intro he
        obtain ⟨p, hpG, (hp | hp) | hp⟩ := hG.equality σ hσ hσn τ hτ hτn
        · exact ⟨p, hpG, hp⟩
        · obtain ⟨π, r, hπ, hpr, hp⟩ := hp
          have hv : value P G π ∈ value P G σ :=
            (mem_value P G σ _).mpr ⟨π, r, G.mem_of_le hpr hpG, hπ, rfl⟩
          rw [he] at hv
          obtain ⟨q, hqG, hq⟩ :=
            ((atomic_truth_semantics Good htests hexists hM false π τ (child_mem_ground hM hσ hπ) hτ (hσn.child hπ) hτn).1 G hgood).mpr hv
          exact False.elim (pfilter_not_pos_neg G (atomic_lower P false π τ) hqG hpG hq hp)
        · obtain ⟨π, r, hπ, hpr, hp⟩ := hp
          have hv : value P G π ∈ value P G τ :=
            (mem_value P G τ _).mpr ⟨π, r, G.mem_of_le hpr hpG, hπ, rfl⟩
          rw [← he] at hv
          obtain ⟨q, hqG, hq⟩ :=
            ((atomic_truth_semantics Good htests hexists hM false π σ (child_mem_ground hM hτ hπ) hσ (hτn.child hπ) hσn).1 G hgood).mpr hv
          exact False.elim (pfilter_not_pos_neg G (atomic_lower P false π σ) hqG hpG hq hp)
  exact ⟨ht, semantics_of_truth P Good hexists (atomic P b σ τ)
    (atomic_lower P b σ τ) (fun _ h => atomic_saturated P b σ τ h) _ ht⟩
termination_by (max σ.rank τ.rank, min σ.rank τ.rank)
decreasing_by
  all_goals first
    | exact sorted_lt_right (child_rank_lt hπ)
    | exact sorted_lt_left (child_rank_lt hπ)
    | have h := sorted_lt_right (a := σ.rank) (child_rank_lt hπ)
      rw [max_comm σ.rank π.rank, min_comm σ.rank π.rank] at h
      exact h

/-- Package the two conclusions once the truth step at the current formula is proved. -/
lemma truth_semantics_stage (Good : Order.PFilter (Condition P) → Prop)
    (hexists : ∀ p : Condition P, ∃ G, Good G ∧ p ∈ G)
    {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M)
    (ht : ∀ G, Good G → ((∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)))) :
    (∀ G, Good G → ((∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)))) ∧
    (∀ p : Condition P, p ∈ force P M φ xs ↔ ∀ G, Good G → p ∈ G →
      φ.Realize Empty.elim (fun i => evalName P M G (xs i))) :=
  ⟨ht, semantics_of_truth P Good hexists (force P M φ xs) (force_lower P M φ xs)
    (force_saturated P M φ xs) _ ht⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \textbf{Equivalence theorem and truth lemma — simultaneous induction.} We prove jointly, by induction on $\varphi$:
-/
/-- The formula induction establishes truth and semantic forcing together at each stage.
The primitive syntax is implication/universal; the derived connective steps are
provided separately by the verified clauses and De Morgan reduction. -/
theorem formula_truth_semantics (Good : Order.PFilter (Condition P) → Prop)
    (htests : ∀ G, Good G → MeetsFormulaTests P M G)
    (hexists : ∀ p : Condition P, ∃ G, Good G ∧ p ∈ G)
    (hM : M.IsTransitive) {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) :
    (∀ G, Good G → ((∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)))) ∧
    (∀ p : Condition P, p ∈ force P M φ xs ↔ ∀ G, Good G → p ∈ G →
      φ.Realize Empty.elim (fun i => evalName P M G (xs i))) := by
  induction φ with
  | falsum =>
    apply truth_semantics_stage P M Good hexists
    intro G _
    simp [force, BoundedFormula.Realize]
  | equal s t =>
    apply truth_semantics_stage P M Good hexists
    intro G hgood
    rw [BoundedFormula.Realize, term_realize, term_realize, Subtype.ext_iff]
    exact (atomic_truth_semantics P M Good htests hexists hM true _ _
      (termName P M s xs).property.1 (termName P M t xs).property.1
      (termName P M s xs).property.2 (termName P M t xs).property.2).1 G hgood
  | rel R ts =>
    apply truth_semantics_stage P M Good hexists
    intro G hgood
    cases R
    simp only [BoundedFormula.Realize, term_realize]
    exact (atomic_truth_semantics P M Good htests hexists hM false _ _
      (termName P M (ts 0) xs).property.1 (termName P M (ts 1) xs).property.1
      (termName P M (ts 0) xs).property.2 (termName P M (ts 1) xs).property.2).1 G hgood
  | imp φ ψ ihφ ihψ =>
    apply truth_semantics_stage P M Good hexists
    intro G hgood
    exact forcingImp_truth G (force_lower P M φ xs) (force_lower P M ψ xs)
      ((ihφ xs).1 G hgood).symm ((ihψ xs).1 G hgood).symm
      ((htests G hgood).implication φ ψ xs)
  | all φ ih =>
    apply truth_semantics_stage P M Good hexists
    intro G hgood
    have hv (τ : Name P M) :
        φ.Realize Empty.elim (Fin.snoc (fun i => evalName P M G (xs i)) (evalName P M G τ)) ↔
        ∃ p ∈ G, p ∈ force P M φ (Fin.snoc xs τ) := by
      have he : evalName P M G ∘ Fin.snoc xs τ =
          Fin.snoc (evalName P M G ∘ xs) (evalName P M G τ) :=
        Fin.comp_snoc (evalName P M G) xs τ
      simp only [Function.comp_def] at he
      rw [← he]
      exact ((ih (Fin.snoc xs τ)).1 G hgood).symm
    have ht := forcingAll_truth G (fun τ => force_lower P M φ (Fin.snoc xs τ)) hv
      ((htests G hgood).universal φ xs)
    constructor
    · intro h x
      obtain ⟨τ, rfl⟩ := evalName_surjective P M G x
      exact ht.mp h τ
    · intro h
      exact ht.mpr (fun τ => h (evalName P M G τ))

end PolishSpaceBook.ForcingFormulas

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-- Instantiate the joint induction with actual ground-model generic filters.
The internal-definability lemmas supply the tests; countability supplies a
generic through each condition. -/
theorem modelGeneric_joint_truth {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (P R : M) [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    (hc : M.toSet.Countable) {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name P.val M) :
    (∀ G, ModelGeneric P.val M G → ((∃ p ∈ G, p ∈ force P.val M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)))) ∧
    (∀ p : Condition P.val, p ∈ force P.val M φ xs ↔
      ∀ G, ModelGeneric P.val M G → p ∈ G →
        φ.Realize Empty.elim (fun i => evalName P.val M G (xs i))) := by
  apply formula_truth_semantics P.val M (ModelGeneric P.val M)
    (fun G hG => modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG)
    ?_ hM φ xs
  intro p
  obtain ⟨G, hpG, hG⟩ := exists_modelGeneric P.val M hc p
  exact ⟨G, hG, hpG⟩

end PolishSpaceBook.SetTheoryModels
