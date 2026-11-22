module

public import PolishSpaceBook.SetTheoryPowerImage

@[expose] public section

/-! # Internal least fixed points of definable monotone operations on a set

Separation constructs the intersection of all internal closed sets. Monotonicity
and closure of the step under Separation make that intersection a fixed point;
no external collection of all subsets is assumed to belong to the model.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters, a bound B, and a candidate T; all step outputs in B must lie in T. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For internal variables define
    $$\begin{aligned}
    \chi_B(T)&\;:\equiv\;\forall y\in B\,
     (\varphi(T,y,\vec p)\longrightarrow y\in T),\\
    \lambda_B(x)&\;:\equiv\;x\in B\land
     \forall T\,(\chi_B(T)\longrightarrow x\in T).
    \end{aligned}$$
    These are first-order formulas with parameters $B,\vec p$; the model itself is not a parameter.
-/
def stepClosedFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    ForcingFormulas.Formula (n + 2) :=
  boundedAll (Fin.last n).castSucc
    ((reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last (n + 1)).castSucc) (Fin.last (n + 2)))).imp
      (memberAt (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc))

lemma realize_stepClosedFormula (M : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (B T : M) :
    (stepClosedFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps B) T) ↔
      ∀ y : M, y.val ∈ B.val → φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps T) y) → y.val ∈ T.val := by
  simp only [stepClosedFormula, realize_boundedAll_model, BoundedFormula.realize_imp,
    realize_memberAt_model, realize_reindex, apply_snoc, Function.comp_def,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- Parameters, a bound B, and x; every internal closed candidate contains x. -/
def leastClosedMemberFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    ForcingFormulas.Formula (n + 2) :=
  ((reindex (stepClosedFormula φ) (Fin.snoc (fun i => i.castSucc.castSucc) (Fin.last (n + 2)))).imp
    (memberAt (Fin.last (n + 1)).castSucc (Fin.last (n + 2)))).all

lemma realize_leastClosedMemberFormula (M : ZFSet.{u}) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (B x : M) :
    (leastClosedMemberFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps B) x) ↔
      ∀ T : M, (∀ y : M, y.val ∈ B.val →
        φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps T) y) → y.val ∈ T.val) → x.val ∈ T.val := by
  simp only [leastClosedMemberFormula, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_memberAt_model, realize_reindex, apply_snoc, Function.comp_def,
    Fin.snoc_castSucc, Fin.snoc_last, realize_stepClosedFormula]

/-- The external description of an intersection quantified over internal candidate sets. -/
def internalLeastClosed (M B : ZFSet.{u}) (step : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  B.sep (fun x => ∀ T ∈ M, (∀ y ∈ B, step T y → y ∈ T) → x ∈ T)

lemma realize_leastClosedMember_step {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (B x : M)
    (step : ZFSet.{u} → ZFSet.{u} → Prop)
    (hφ : ∀ T y : M, y.val ∈ B.val →
      (φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps T) y) ↔ step T.val y.val)) :
    (leastClosedMemberFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps B) x) ↔
      ∀ T ∈ M, (∀ y ∈ B.val, step T y → y ∈ T) → x.val ∈ T := by
  rw [realize_leastClosedMemberFormula]
  constructor
  · intro h T hT hclosed
    exact h ⟨T, hT⟩ (fun y hy hs => hclosed y.val hy ((hφ ⟨T, hT⟩ y hy).mp hs))
  · intro h T hclosed
    apply h T.val T.property
    intro y hy hs
    exact hclosed ⟨y, hM.mem_trans hy B.property⟩ hy
      ((hφ T ⟨y, hM.mem_trans hy B.property⟩ hy).mpr hs)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Transitivity and the hypothesis on $\varphi$ identify the interpretation of $\lambda_B$ with membership in $C$.
    Separation gives $C\in M$. It also gives $\Phi(S)\in M$ for every $S\in M$.
    Minimality follows directly from the definition of $C$.
-/
lemma internalLeastClosed_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (hsep : M ⊨ separationSentence (leastClosedMemberFormula φ))
    (ps : Fin n → M) (B : M) (step : ZFSet.{u} → ZFSet.{u} → Prop)
    (hφ : ∀ T y : M, y.val ∈ B.val →
      (φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps T) y) ↔ step T.val y.val)) :
    internalLeastClosed M B.val step ∈ M := by
  apply separation_mem_of_absolute hM (leastClosedMemberFormula φ) hsep (Fin.snoc ps B) B.property
  intro x _
  exact realize_leastClosedMember_step hM φ ps B x step hφ

lemma internalLeastClosed_subset {M B : ZFSet.{u}} {step : ZFSet.{u} → ZFSet.{u} → Prop} :
    internalLeastClosed M B step ⊆ B := fun _ hx => (ZFSet.mem_sep.mp hx).1

lemma internalLeastClosed_minimal {M B T : ZFSet.{u}} {step : ZFSet.{u} → ZFSet.{u} → Prop}
    (hT : T ∈ M) (hclosed : ∀ y ∈ B, step T y → y ∈ T) : internalLeastClosed M B step ⊆ T :=
  fun _ hx => (ZFSet.mem_sep.mp hx).2 T hT hclosed

/-- The least internal closed subset is a genuine fixed point, not just an internal approximation. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For any $T\in M$ with $\Phi(T)\IncludedIn T$, minimality and monotonicity give
    $$\Phi(C)\IncludedIn\Phi(T)\IncludedIn T.$$
    Since $\Phi(C)\IncludedIn B$, it follows that $\Phi(C)\IncludedIn C$.
    Monotonicity then gives $\Phi(\Phi(C))\IncludedIn\Phi(C)$.
    The set $\Phi(C)$ belongs to the model, so it is itself one of the closed candidates in the definition of $C$.
    Minimality gives $C\IncludedIn\Phi(C)$, proving equality. Only internal candidates were intersected;
    no closure under the external power set was used.
    \end{proof}
-/
theorem internalLeastClosed_fixed {M B : ZFSet.{u}} {step : ZFSet.{u} → ZFSet.{u} → Prop}
    (hmono : ∀ S T : ZFSet.{u}, S ⊆ T → ∀ y ∈ B, step S y → step T y)
    (hC : internalLeastClosed M B step ∈ M)
    (hstep : ∀ S ∈ M, B.sep (step S) ∈ M) :
    B.sep (step (internalLeastClosed M B step)) = internalLeastClosed M B step := by
  let C := internalLeastClosed M B step
  have hFC : B.sep (step C) ⊆ C := by
    intro y hy
    obtain ⟨hyB, hsy⟩ := ZFSet.mem_sep.mp hy
    apply ZFSet.mem_sep.mpr
    refine ⟨hyB, ?_⟩
    intro T hT hclosed
    exact hclosed y hyB (hmono C T (internalLeastClosed_minimal hT hclosed) y hyB hsy)
  have hCF : C ⊆ B.sep (step C) := by
    apply internalLeastClosed_minimal (hstep C hC)
    intro y hyB hsy
    exact ZFSet.mem_sep.mpr ⟨hyB, hmono (B.sep (step C)) C hFC y hyB hsy⟩
  exact ZFSet.ext (fun _ => ⟨fun h => hFC h, fun h => hCF h⟩)

/-- Definability and monotonicity alone suffice for an internal fixed point on a fixed bound. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal least fixed points
-/
theorem internal_definable_fixed_point {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (B : M)
    (step : ZFSet.{u} → ZFSet.{u} → Prop)
    (hφ : ∀ T y : M, y.val ∈ B.val →
      (φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps T) y) ↔ step T.val y.val))
    (hmono : ∀ S T : ZFSet.{u}, S ⊆ T → ∀ y ∈ B.val, step S y → step T y) :
    internalLeastClosed M B.val step ∈ M ∧
      B.val.sep (step (internalLeastClosed M B.val step)) = internalLeastClosed M B.val step := by
  have hC := internalLeastClosed_mem hM φ (hsep _) ps B step hφ
  refine ⟨hC, internalLeastClosed_fixed hmono hC ?_⟩
  intro S hS
  apply separation_mem_of_absolute hM φ (hsep _) (Fin.snoc ps ⟨S, hS⟩) B.property
  intro y hy
  exact hφ ⟨S, hS⟩ y hy

end PolishSpaceBook.SetTheoryModels
