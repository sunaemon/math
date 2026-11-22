module

public import PolishSpaceBook.LogicActions
public import Mathlib.ModelTheory.Semantics

@[expose] public section

/-! # Countable infinitary formulas with finite variable contexts

Terms and structures are mathlib's first-order terms and structures. The formula
syntax adds countable conjunction in a fixed finite context; quantification
removes one variable at a time. The semantic proofs follow structural induction.
-/

namespace PolishSpaceBook.InfinitaryLogic

open Set Topology FirstOrder FirstOrder.Language
open LogicActions
open scoped PointwisePerm

universe u v
variable (L : FirstOrder.Language.{u, v})

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The logic action has an exact syntactic counterpart in the infinitary logic $\LCountableInfinitaryLogic$.
    We first specify its formulas and their interpretation.
-/
/-- Infinitary formulas whose free variables lie in the displayed finite context. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: definition
  excerpt: |
    For each $n\in\omega$, consider formulas whose free variables are among $x_0,\ldots,x_{n-1}$. They are generated simultaneously for all $n$
-/
inductive Formula : ℕ → Type (max u v)
  | falsum {n} : Formula n
  | equal {n} (t s : L.Term (Fin n)) : Formula n
  | rel {n k} (r : L.Relations k) (ts : Fin k → L.Term (Fin n)) : Formula n
  | neg {n} (φ : Formula n) : Formula n
  | conj {n} (φ : ℕ → Formula n) : Formula n
  | ex {n} (φ : Formula (n + 1)) : Formula n

variable {L}

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    Interpretation is defined by structural recursion. Terms and atomic formulas have their usual first-order
    interpretations; $\bot$ is false, negation reverses truth, and a countable conjunction holds exactly when all its
    conjuncts hold. An existential formula holds under a given assignment exactly when some value for the last variable
    makes its body true. This definition applies to any $L$-structure.
    Free variables may be renamed or identified: under a map from one finite variable context to another, rename the
    variables in each term, commute the operation with negation and conjunction, and keep each newly bound variable fresh.
    Structural induction shows that evaluating the renamed formula under an assignment gives the same truth value as
    evaluating the original formula under the pulled-back assignment.
-/
/-- Realization uses the usual term semantics and appends each quantified value. -/
def Formula.Realize {M : Type*} [L.Structure M] :
    {n : ℕ} → Formula L n → (Fin n → M) → Prop
  | _, .falsum, _ => False
  | _, .equal t s, a => t.realize a = s.realize a
  | _, .rel r ts, a => Structure.RelMap r (fun i => (ts i).realize a)
  | _, .neg φ, a => ¬ φ.Realize a
  | _, .conj φ, a => ∀ k, (φ k).Realize a
  | _, .ex φ, a => ∃ b, φ.Realize (Fin.snoc a b)

/-- Countable disjunction is obtained by De Morgan duality. -/
def Formula.disj {n} (φ : ℕ → Formula L n) : Formula L n :=
  .neg (.conj fun k => .neg (φ k))

/-- Universal quantification is the dual of existential quantification. -/
def Formula.all {n} (φ : Formula L (n + 1)) : Formula L n := .neg (.ex (.neg φ))

@[simp] theorem Formula.realize_disj {M : Type*} [L.Structure M] {n}
    (φ : ℕ → Formula L n) (a : Fin n → M) :
    (Formula.disj φ).Realize a ↔ ∃ k, (φ k).Realize a := by
  classical
  simp [disj, Realize]

@[simp] theorem Formula.realize_all {M : Type*} [L.Structure M] {n}
    (φ : Formula L (n + 1)) (a : Fin n → M) :
    φ.all.Realize a ↔ ∀ b, φ.Realize (Fin.snoc a b) := by
  classical
  simp [all, Realize]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    An isomorphism preserves term values and atomic truth. Structural induction extends this to negation and countable
    conjunction. At an existential quantifier, transport a witness by the isomorphism; the reverse implication uses
    its surjectivity. Hence truth is preserved when the assignment is transported by an isomorphism.
    Sentences have no assigned free variables, so their satisfaction sets are isomorphism-invariant.
-/
/-- Isomorphisms preserve infinitary satisfaction, including all finite contexts. -/
theorem Formula.realize_equiv {M N : Type*} [L.Structure M] [L.Structure N]
    (e : L.Equiv M N) {n} (φ : Formula L n) (a : Fin n → M) :
    φ.Realize (e ∘ a) ↔ φ.Realize a := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [Realize, HomClass.realize_term, e.injective.eq_iff]
  | rel r ts =>
    simp only [Realize]
    simp_rw [HomClass.realize_term]
    exact e.map_rel r (fun i => (ts i).realize a)
  | neg φ ih => exact not_congr (ih a)
  | conj φ ih => exact forall_congr' fun k => ih k a
  | ex φ ih =>
    change (∃ b, φ.Realize (Fin.snoc (e ∘ a) b)) ↔ ∃ b, φ.Realize (Fin.snoc a b)
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨c, rfl⟩ := e.surjective b
      exact ⟨c, (ih (Fin.snoc a c)).mp (by simpa only [Fin.comp_snoc] using hb)⟩
    · rintro ⟨b, hb⟩
      exact ⟨e b, by simpa only [Fin.comp_snoc] using (ih (Fin.snoc a b)).mpr hb⟩

/-- Lift a variable map past the freshly bound last variable. -/
def liftVariables {n m} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.snoc (Fin.castSucc ∘ f) (Fin.last m)

/-- Renaming respects binders, including maps that identify free variables. -/
def Formula.rename : {n m : ℕ} → Formula L n → (Fin n → Fin m) → Formula L m
  | _, _, .falsum, _ => .falsum
  | _, _, .equal t s, f => .equal (t.relabel f) (s.relabel f)
  | _, _, .rel r ts, f => .rel r (fun i => (ts i).relabel f)
  | _, _, .neg φ, f => .neg (φ.rename f)
  | _, _, .conj φ, f => .conj fun k => (φ k).rename f
  | _, _, .ex φ, f => .ex (φ.rename (liftVariables f))

theorem snoc_comp_liftVariables {M : Type*} {n m} (a : Fin m → M) (b : M)
    (f : Fin n → Fin m) :
    Fin.snoc a b ∘ liftVariables f = Fin.snoc (a ∘ f) b := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftVariables, Function.comp_def]

/-- Satisfaction after renaming is satisfaction under the pulled-back assignment. -/
theorem Formula.realize_rename {M : Type*} [L.Structure M] {n} (φ : Formula L n) :
    ∀ {m} (f : Fin n → Fin m) (a : Fin m → M),
      (φ.rename f).Realize a ↔ φ.Realize (a ∘ f) := by
  induction φ with
  | falsum => intros; rfl
  | equal t s => intros; simp only [rename, Realize, Term.realize_relabel]
  | rel r ts => intros; simp only [rename, Realize, Term.realize_relabel]
  | neg φ ih => exact fun f a => not_congr (ih f a)
  | conj φ ih => exact fun f a => forall_congr' fun k => ih k f a
  | ex φ ih =>
    intro m f a
    change (∃ b, (φ.rename (liftVariables f)).Realize (Fin.snoc a b)) ↔ _
    simp_rw [ih, snoc_comp_liftVariables]
    rfl

/-- Evaluate an ordinary term in the structure selected by the model code. -/
def termValue {n} (t : L.Term (Fin n)) (M : ModelCode L) (a : Fin n → ℕ) : ℕ :=
  t.realize (M := ModelCarrier L M) a

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For a fixed assignment, the value of each term depends continuously on $M$. For a variable this is constant.
    For a function application, first fix the values of its finitely many argument terms in a neighborhood of $M$,
    and then fix the single function-table coordinate at that tuple. Induction on terms proves the assertion,
    including nested function applications. Equality and relation formulas therefore define clopen sets.
-/
/-- Evaluation is continuous even when terms contain nested function symbols. -/
theorem continuous_termValue {n} (t : L.Term (Fin n)) (a : Fin n → ℕ) :
    Continuous (fun M : ModelCode L => termValue t M a) := by
  induction t with
  | var i => exact continuous_const
  | @func k f ts ih =>
    have hv : Continuous (fun z : (FunIndex L → ℕ) × FunIndex L => z.1 z.2) :=
      continuous_prod_of_discrete_right.mpr fun i => continuous_apply i
    have ht : Continuous (fun M : ModelCode L =>
        (⟨⟨k, f⟩, fun i => termValue (ts i) M a⟩ : FunIndex L)) :=
      continuous_of_discreteTopology.comp (continuous_pi ih)
    exact hv.comp (continuous_snd.prodMk ht)

/-- Satisfaction with the chosen interpretation; the assignment is a finite tuple. -/
def Formula.Satisfies {n} (φ : Formula L n) (M : ModelCode L) (a : Fin n → ℕ) : Prop :=
  φ.Realize (M := ModelCarrier L M) a

local instance : MeasurableSpace (ModelCode L) := borel _
local instance : BorelSpace (ModelCode L) := ⟨rfl⟩

/-- Atomic equality defines a clopen subset of the logic space. -/
theorem isClopen_equal {n} (t s : L.Term (Fin n)) (a : Fin n → ℕ) :
    IsClopen {M : ModelCode L | (Formula.equal t s).Satisfies M a} := by
  have h := (continuous_termValue t a).prodMk (continuous_termValue s a)
  exact (isClopen_discrete {p : ℕ × ℕ | p.1 = p.2}).preimage h

/-- Atomic relation formulas define clopen sets, also for arity zero. -/
theorem isClopen_rel {n k} (r : L.Relations k) (ts : Fin k → L.Term (Fin n))
    (a : Fin n → ℕ) : IsClopen {M : ModelCode L | (Formula.rel r ts).Satisfies M a} := by
  have hv : Continuous (fun z : (RelIndex L → Bool) × RelIndex L => z.1 z.2) :=
    continuous_prod_of_discrete_right.mpr fun i => continuous_apply i
  have ht : Continuous (fun M : ModelCode L =>
      (⟨⟨k, r⟩, fun i => termValue (ts i) M a⟩ : RelIndex L)) :=
    continuous_of_discreteTopology.comp (continuous_pi fun i => continuous_termValue (ts i) a)
  exact (isClopen_discrete ({true} : Set Bool)).preimage (hv.comp (continuous_fst.prodMk ht))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Now use structural induction on formulas. Falsity gives the empty set, negation gives complement,
    and countable conjunction gives countable intersection. Existential quantification gives a countable union:
    for each $b\in\NN$, extend the fixed assignment by assigning $b$ to the last variable and apply the induction
    hypothesis to the body. Thus each satisfaction set is Borel.
-/
/-- Each formula with a fixed finite assignment defines a Borel set of structures. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    Fix a finite tuple $\bar a$ of natural numbers. For every formula $\varphi$ in the corresponding context,
-/
theorem Formula.measurableSet_satisfies {n} (φ : Formula L n) (a : Fin n → ℕ) :
    MeasurableSet {M : ModelCode L | φ.Satisfies M a} := by
  induction φ with
  | falsum => exact MeasurableSet.empty
  | equal t s => exact (isClopen_equal t s a).isClosed.measurableSet
  | rel r ts => exact (isClopen_rel r ts a).isClosed.measurableSet
  | neg φ ih => exact (ih a).compl
  | conj φ ih =>
    change MeasurableSet {M : ModelCode L | ∀ k, (φ k).Satisfies M a}
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter fun k => ih k a
  | ex φ ih =>
    change MeasurableSet {M : ModelCode L | ∃ b, φ.Satisfies M (Fin.snoc a b)}
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion fun b => ih (Fin.snoc a b)

/-- A sentence has no free variables. -/
abbrev Sentence (L : FirstOrder.Language) := Formula L 0

/-- The class of countable models of a sentence. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    Fix a finite tuple $\bar a$ of natural numbers. For every formula $\varphi$ in the corresponding context,
-/
def models (φ : Sentence L) : Set (ModelCode L) := {M | φ.Satisfies M Fin.elim0}

theorem measurableSet_models (φ : Sentence L) : MeasurableSet (models φ) :=
  φ.measurableSet_satisfies Fin.elim0

/-- The Borel set defined by a sentence is invariant under the logic action. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    Fix a finite tuple $\bar a$ of natural numbers. For every formula $\varphi$ in the corresponding context,
-/
theorem smul_mem_models_iff (φ : Sentence L) (p : Equiv.Perm ℕ) (M : ModelCode L) :
    p • M ∈ models φ ↔ M ∈ models φ := by
  have h := φ.realize_equiv (relabelIso L p M) Fin.elim0
  have ha : (relabelIso L p M) ∘ Fin.elim0 = Fin.elim0 := Subsingleton.elim _ _
  rw [ha] at h
  exact h

end PolishSpaceBook.InfinitaryLogic
