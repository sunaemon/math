module

public import PolishSpaceBook.SetTheoryReflectionBounds
public import PolishSpaceBook.ForcingFormulas

@[expose] public section

/-! # Finite reflection by bounds for quantified subformulas

Use mathlib's implication/universal-quantifier syntax. A failed universal
formula supplies a least-rank counterexample, which is a witness for its
negated matrix. This is the same witness-bound construction as for existentials.
-/
noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas Order
universe u

instance membershipUniverse : membershipLanguage.Structure ZFSet.{u} where
  RelMap | .mem => fun xs => xs 0 ∈ xs 1

/-- A recursive common bound for the witnesses of quantified subformulas. -/
def formulaReflectionBound : {n : ℕ} → ForcingFormulas.Formula n → Ordinal.{u} → Ordinal.{u}
  | _, .falsum, _ => 0
  | _, .equal _ _, _ => 0
  | _, .rel _ _, _ => 0
  | _, .imp φ ψ, β => max (formulaReflectionBound φ β) (formulaReflectionBound ψ β)
  | _, .all φ, β => max (formulaReflectionBound φ β)
      (reflectionWitnessBound (fun xs x => ¬ φ.Realize Empty.elim (Fin.snoc xs x)) β)

/-- Every finite tuple in a limit stage already lies in an earlier stage. -/
theorem tuple_bounded_below_limit {n : ℕ} {α : Ordinal.{u}} (hα : IsSuccLimit α)
    (xs : Fin n → ZFSet.vonNeumann α) :
    ∃ β < α, ∀ i, (xs i).val ∈ ZFSet.vonNeumann β := by
  let β := Finset.univ.sup (fun i => (xs i).val.rank + 1)
  refine ⟨β, ?_, ?_⟩
  · apply (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr hα.ne_bot)).mpr
    intro i _
    exact hα.succ_lt (ZFSet.mem_vonNeumann.mp (xs i).property)
  · intro i
    apply ZFSet.mem_vonNeumann.mpr
    exact (Order.lt_succ _).trans_le (Finset.le_sup (f := fun i => (xs i).val.rank + 1)
      (Finset.mem_univ i))

lemma term_realize_stage {n : ℕ} (α : Ordinal.{u})
    (t : membershipLanguage.Term (Empty ⊕ Fin n)) (xs : Fin n → ZFSet.vonNeumann α) :
    t.realize (Sum.elim Empty.elim (fun i => (xs i).val)) =
      (t.realize (Sum.elim Empty.elim xs)).val := by
  cases t with
  | var x => cases x with
    | inl e => exact e.elim
    | inr i => rfl
  | func f _ => exact f.elim

/-- Closure under the bounds of subformulas gives absoluteness by structural induction. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    Fix $\alpha\in C$ and prove reflection by induction on the subformulas. Atomic formulas use the actual
    membership and equality relations on $V_\alpha$; implication and falsity follow immediately from the induction
    hypotheses. For a universal formula, truth in $V$ implies truth in $V_\alpha$ by applying the induction hypothesis
    to each element of $V_\alpha$. Conversely, suppose the formula holds in $V_\alpha$ but fails in $V$, with parameters
    $\vec a\in V_\alpha$. Since the tuple is finite and $\alpha$ is a limit, choose $\beta<\alpha$ with
    $\vec a\in V_\beta$. A least-rank counterexample $x$ satisfies
    $$\mathrm{rank}(x)<F_\psi(\beta)\le F(\beta)<\alpha,$$
    so $x\in V_\alpha$. The induction hypothesis for the matrix makes this a counterexample inside $V_\alpha$ as well,
    a contradiction. Thus every formula in $\Phi$ is reflected.
-/
theorem formula_reflects_of_bounds {n : ℕ} (φ : ForcingFormulas.Formula n)
    (α : Ordinal.{u}) (hα : IsSuccLimit α)
    (hbound : ∀ β < α, formulaReflectionBound φ β < α) :
    ∀ xs : Fin n → ZFSet.vonNeumann α,
      φ.Realize Empty.elim (fun i => (xs i).val) ↔ φ.Realize Empty.elim xs := by
  induction φ with
  | falsum => intro xs; rfl
  | equal t s =>
    intro xs
    simp only [BoundedFormula.Realize, term_realize_stage, Subtype.val_inj]
  | rel R ts =>
    cases R
    intro xs
    change (ts 0).realize (Sum.elim Empty.elim (fun i => (xs i).val)) ∈
      (ts 1).realize (Sum.elim Empty.elim (fun i => (xs i).val)) ↔
      ((ts 0).realize (Sum.elim Empty.elim xs)).val ∈ ((ts 1).realize (Sum.elim Empty.elim xs)).val
    rw [term_realize_stage, term_realize_stage]
  | imp φ ψ ihφ ihψ =>
    intro xs
    have hφ : ∀ β < α, formulaReflectionBound φ β < α :=
      fun β hβ => (le_max_left _ _).trans_lt (hbound β hβ)
    have hψ : ∀ β < α, formulaReflectionBound ψ β < α :=
      fun β hβ => (le_max_right _ _).trans_lt (hbound β hβ)
    exact imp_congr (ihφ hφ xs) (ihψ hψ xs)
  | @all n φ ih =>
    intro xs
    have hφ : ∀ β < α, formulaReflectionBound φ β < α :=
      fun β hβ => (le_max_left _ _).trans_lt (hbound β hβ)
    have he (x : ZFSet.vonNeumann α) :
        φ.Realize Empty.elim (Fin.snoc (fun i => (xs i).val) x.val) ↔
        φ.Realize Empty.elim (Fin.snoc xs x) := by
      have hh := ih hφ (Fin.snoc xs x)
      change φ.Realize Empty.elim (Subtype.val ∘ Fin.snoc xs x) ↔ _ at hh
      rw [Fin.comp_snoc] at hh
      exact hh
    constructor
    · intro h x
      exact (he x).mp (h x.val)
    · intro h x
      classical
      by_contra hx
      obtain ⟨β, hβ, hxs⟩ := tuple_bounded_below_limit hα xs
      let ys : Fin n → ZFSet.vonNeumann β := fun i => ⟨(xs i).val, hxs i⟩
      obtain ⟨y, hy, hyr⟩ := reflectionWitnessBound_spec
        (fun zs z => ¬ φ.Realize Empty.elim (Fin.snoc zs z)) β ys ⟨x, hx⟩
      have hyα : y ∈ ZFSet.vonNeumann α := ZFSet.mem_vonNeumann.mpr
        (hyr.trans ((le_max_right _ _).trans_lt (hbound β hβ)))
      exact hy ((he ⟨y, hyα⟩).mpr (h ⟨y, hyα⟩))

/-- A finite family may contain formulas with different numbers of parameters. -/
def finiteReflectionBound (Φ : List (Σ n, ForcingFormulas.Formula n)) (β : Ordinal.{u}) : Ordinal.{u} :=
  (Φ.map (fun φ => formulaReflectionBound φ.2 β)).foldr max 0

theorem formula_le_finiteReflectionBound (Φ : List (Σ n, ForcingFormulas.Formula n))
    {φ : Σ n, ForcingFormulas.Formula n} (hφ : φ ∈ Φ) (β : Ordinal.{u}) :
    formulaReflectionBound φ.2 β ≤ finiteReflectionBound Φ β := by
  induction Φ with
  | nil => simp at hφ
  | cons ψ Φ ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact le_max_left _ _
    · exact (ih hφ).trans (le_max_right _ _)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: theorem
  title: finite reflection
-/
theorem finite_reflection (Φ : List (Σ n, ForcingFormulas.Formula n)) :
    ∃ C : Set Ordinal.{u}, IsClosed C ∧ (∀ γ, ∃ α ∈ C, γ < α) ∧
      ∀ α ∈ C, ∀ φ ∈ Φ, ∀ xs : Fin φ.1 → ZFSet.vonNeumann α,
        φ.2.Realize Empty.elim (fun i => (xs i).val) ↔ φ.2.Realize Empty.elim xs := by
  refine ⟨reflectionClosurePoints (finiteReflectionBound Φ),
    reflectionClosurePoints_closed _, reflectionClosurePoints_unbounded _, ?_⟩
  intro α hα φ hφ
  apply formula_reflects_of_bounds φ.2 α (reflectionClosurePoints_isSuccLimit hα)
  intro β hβ
  exact ((formula_le_finiteReflectionBound Φ hφ β).trans
    (le_reflectionMajorant _ β)).trans_lt (hα.2 β hβ)

/-- Reflection transfers every chosen finite list of ambient true sentences. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    Finally, apply reflection to any chosen finite list of sentences true in $V$.
    Every reflecting stage satisfies those sentences. In particular, this applies to any finite list of ZFC axioms
    and schema instances.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is the theorem behind the common forcing convention "work in a sufficiently large finite fragment of ZFC."
    Reflection supplies transitive sets $V_\alpha$ satisfying any prescribed finite fragment; compactness, downward
    Löwenheim--Skolem, and Mostowski collapse then explain the countable-transitive-model reduction used in
    §{sec:internal-model-closure}.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finite reflection is a theorem of ZFC and gives, separately
    for each finite fragment, some transitive $V_\alpha$ satisfying that fragment.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Reflection gives only the finite amount of ZFC needed for the
    argument at hand, but it does so inside ordinary ZFC.
-/
theorem finite_true_sentences_reflect (Φ : List membershipLanguage.Sentence)
    (hΦ : ∀ φ ∈ Φ, ZFSet.{u} ⊨ φ) (γ : Ordinal.{u}) :
    ∃ α > γ, ∀ φ ∈ Φ, ZFSet.vonNeumann α ⊨ φ := by
  let Ψ : List (Σ n, ForcingFormulas.Formula n) := Φ.map (fun φ => ⟨0, φ⟩)
  obtain ⟨C, _, hC, hreflect⟩ := finite_reflection.{u} Ψ
  obtain ⟨α, hα, hγα⟩ := hC γ
  refine ⟨α, hγα, ?_⟩
  intro φ hφ
  have hmem : (⟨0, φ⟩ : Σ n, ForcingFormulas.Formula n) ∈ Ψ := List.mem_map.mpr ⟨φ, hφ, rfl⟩
  have he := hreflect α hα ⟨0, φ⟩ hmem Fin.elim0
  have sentence_iff (M : Type (u + 1)) [membershipLanguage.Structure M]
      (v : Fin 0 → M) : (M ⊨ φ) ↔ BoundedFormula.Realize φ (Empty.elim : Empty → M) v := by
    unfold Sentence.Realize FirstOrder.Language.Formula.Realize
    rw [Subsingleton.elim (default : Empty → M) Empty.elim,
      Subsingleton.elim (default : Fin 0 → M) v]
  apply (sentence_iff _ Fin.elim0).mpr
  exact he.mp ((sentence_iff _ _).mp (hΦ φ hφ))

/-- A prescribed set of parameters fits in the same reflecting stage. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a transitive model $M$ of a sufficiently large finite fragment of ZFC. Here "sufficiently large" means: large enough
    to include the particular ZFC axioms and schema instances used in the forcing construction under discussion. The finite
    reflection theorem in §{sec:zfc-cumulative-hierarchy} justifies this convention. Given any prescribed finite fragment,
    and any set of parameters that must be present, reflection gives some transitive $V_\alpha$ satisfying that fragment and
    containing those parameters.
-/
theorem finite_true_sentences_reflect_parameters (Φ : List membershipLanguage.Sentence)
    (hΦ : ∀ φ ∈ Φ, ZFSet.{u} ⊨ φ) (P : ZFSet.{u}) :
    ∃ α : Ordinal.{u}, P ∈ ZFSet.vonNeumann α ∧ P ⊆ ZFSet.vonNeumann α ∧
      ∀ φ ∈ Φ, ZFSet.vonNeumann α ⊨ φ := by
  obtain ⟨α, hα, hΦα⟩ := finite_true_sentences_reflect Φ hΦ P.rank
  exact ⟨α, ZFSet.mem_vonNeumann.mpr hα,
    fun x hx => ZFSet.mem_vonNeumann.mpr ((ZFSet.rank_lt_of_mem hx).trans hα), hΦα⟩

end PolishSpaceBook.SetTheoryModels
