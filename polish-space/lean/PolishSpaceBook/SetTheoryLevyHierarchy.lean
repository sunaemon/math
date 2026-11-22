module

public import PolishSpaceBook.SetTheoryZFCConsistency
public import PolishSpaceBook.FirstOrderProofCongruence

@[expose] public section

/-! # All finite Levy levels, using genuine ZFC-provable equivalence -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas NamedFirstOrder

/-- Equivalence is a derivable biconditional in the actual translated full ZFC theory. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the positive levels, we also allow formulas provably equivalent over ZFC to these forms.
-/
def ZFCFormulaEquivalent {n : ℕ} (φ ψ : ForcingFormulas.Formula n) : Prop :=
  ProvesFrom namedFullZFCTheory (AlphaFormula.biimp
    (AlphaFormula.mk (boundedToNamed φ)) (AlphaFormula.mk (boundedToNamed ψ)))

theorem ZFCFormulaEquivalent.refl {n : ℕ} (φ : ForcingFormulas.Formula n) :
    ZFCFormulaEquivalent φ φ := by
  classical
  refine ⟨∅, by simp, ?_⟩
  exact Derives.andIntro (Derives.impIntro (Derives.hyp ∅ _))
    (Derives.impIntro (Derives.hyp ∅ _))

/-- A provable equivalence is true in every model, with every parameter assignment retained. -/
theorem ZFCFormulaEquivalent.sound {n : ℕ} {φ ψ : ForcingFormulas.Formula n}
    (h : ZFCFormulaEquivalent φ ψ) {M : Type*} [membershipLanguage.Structure M]
    (hM : M ⊨ fullZFCTheory) (s : ℕ → M) :
    φ.Realize Empty.elim (fun i => s i.val) ↔ ψ.Realize Empty.elim (fun i => s i.val) := by
  have ht := NamedFirstOrder.ProvesFrom.sound h s (fun θ hθ => namedFullZFCTheory_realize hM s hθ)
  simp only [AlphaFormula.biimp, AlphaFormula.realize_binary, Connective.eval,
    AlphaFormula.realize_mk, realize_boundedToNamed] at ht
  exact ⟨ht.1, ht.2⟩

/-- A finite existential prefix, possibly empty, over a specified class of matrices. -/
inductive ExistentialPrefix (P : {n : ℕ} → ForcingFormulas.Formula n → Prop) :
    {n : ℕ} → ForcingFormulas.Formula n → Prop
  | base {n} {φ : ForcingFormulas.Formula n} : P φ → ExistentialPrefix P φ
  | ex {n} {φ : ForcingFormulas.Formula (n + 1)} :
      ExistentialPrefix P φ → ExistentialPrefix P φ.ex

/-- A finite universal prefix over a specified class of matrices. -/
inductive UniversalPrefix (P : {n : ℕ} → ForcingFormulas.Formula n → Prop) :
    {n : ℕ} → ForcingFormulas.Formula n → Prop
  | base {n} {φ : ForcingFormulas.Formula n} : P φ → UniversalPrefix P φ
  | all {n} {φ : ForcingFormulas.Formula (n + 1)} :
      UniversalPrefix P φ → UniversalPrefix P φ.all

inductive LevyPolarity where
  | sigma | pi

/-- At positive levels the matrix belongs to the opposite preceding level, and equivalence
must come from an actual ZFC derivation. Bounded closure is not built into this definition. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{Levy hierarchy}{Lévy hierarchy} classifies set-theoretic formulas by quantifier complexity:
-/
def LevyClass : LevyPolarity → ℕ → {n : ℕ} → ForcingFormulas.Formula n → Prop
  | _, 0, _, φ => IsDeltaZero φ
  | .sigma, k + 1, _, φ => ∃ ψ, ExistentialPrefix (fun {m} (χ : ForcingFormulas.Formula m) => LevyClass .pi k χ) ψ ∧
      ZFCFormulaEquivalent φ ψ
  | .pi, k + 1, _, φ => ∃ ψ, UniversalPrefix (fun {m} (χ : ForcingFormulas.Formula m) => LevyClass .sigma k χ) ψ ∧
      ZFCFormulaEquivalent φ ψ

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\Delta_0 = \Sigma_0 = \Pi_0$: only bounded quantifiers $(\forall x \in y)$ and $(\exists x \in y)$.
    *   $\Sigma_{n+1}$: $\exists x_1\cdots\exists x_k\, \varphi$ with $\varphi \in \Pi_n$.
    *   $\Pi_{n+1}$: $\forall x_1\cdots\forall x_k\, \varphi$ with $\varphi \in \Sigma_n$.
    *   $\Delta_{n+1}$: provably equivalent to both a $\Sigma_{n+1}$ and a $\Pi_{n+1}$ formula in ZFC.
-/
def LevySigma (k : ℕ) {n : ℕ} (φ : ForcingFormulas.Formula n) : Prop := LevyClass .sigma k φ
def LevyPi (k : ℕ) {n : ℕ} (φ : ForcingFormulas.Formula n) : Prop := LevyClass .pi k φ

def LevyDelta (k : ℕ) {n : ℕ} (φ : ForcingFormulas.Formula n) : Prop :=
  match k with
  | 0 => IsDeltaZero φ
  | k + 1 => LevySigma (k + 1) φ ∧ LevyPi (k + 1) φ

/-- All three zero levels are exactly the bounded formulas. -/
theorem levy_zero {n : ℕ} (φ : ForcingFormulas.Formula n) :
    (LevySigma 0 φ ↔ IsDeltaZero φ) ∧ (LevyPi 0 φ ↔ IsDeltaZero φ) ∧
      (LevyDelta 0 φ ↔ IsDeltaZero φ) := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem LevySigma.of_prefix {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (h : ExistentialPrefix (fun {m} (χ : ForcingFormulas.Formula m) => LevyPi k χ) φ) : LevySigma (k + 1) φ :=
  ⟨φ, h, ZFCFormulaEquivalent.refl φ⟩

theorem LevyPi.of_prefix {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (h : UniversalPrefix (fun {m} (χ : ForcingFormulas.Formula m) => LevySigma k χ) φ) : LevyPi (k + 1) φ :=
  ⟨φ, h, ZFCFormulaEquivalent.refl φ⟩

/-- Finite parameter tuples can be used directly; the extra value extends the assignment only. -/
theorem ZFCFormulaEquivalent.sound_fin {n : ℕ} {φ ψ : ForcingFormulas.Formula n}
    (h : ZFCFormulaEquivalent φ ψ) {M : Type*} [membershipLanguage.Structure M]
    (hM : M ⊨ fullZFCTheory) (d : M) (xs : Fin n → M) :
    φ.Realize Empty.elim xs ↔ ψ.Realize Empty.elim xs := by
  let s (k : ℕ) : M := if hk : k < n then xs ⟨k, hk⟩ else d
  have he : (fun i : Fin n => s i.val) = xs := by
    funext i
    simp only [s, dite_eq_left i.isLt]
  simpa only [he] using ZFCFormulaEquivalent.sound h hM s

/-- The new finite-prefix interface agrees with the existing syntactic Sigma-one class. -/
theorem existentialPrefix_delta_iff {n : ℕ} (φ : ForcingFormulas.Formula n) :
    ExistentialPrefix IsDeltaZero φ ↔ IsSigmaOne φ := by
  constructor
  · intro h
    induction h with
    | base h => exact .delta h
    | ex _ ih => exact .ex ih
  · intro h
    induction h with
    | delta h => exact .base h
    | ex _ ih => exact .ex ih

/-- The same agreement holds for universal prefixes and Pi-one. -/
theorem universalPrefix_delta_iff {n : ℕ} (φ : ForcingFormulas.Formula n) :
    UniversalPrefix IsDeltaZero φ ↔ IsPiOne φ := by
  constructor
  · intro h
    induction h with
    | base h => exact .delta h
    | all _ ih => exact .all ih
  · intro h
    induction h with
    | delta h => exact .base h
    | all _ ih => exact .all ih

theorem levySigma_one_iff {n : ℕ} (φ : ForcingFormulas.Formula n) :
    LevySigma 1 φ ↔ ∃ ψ, IsSigmaOne ψ ∧ ZFCFormulaEquivalent φ ψ := by
  change (∃ ψ, ExistentialPrefix IsDeltaZero ψ ∧ ZFCFormulaEquivalent φ ψ) ↔ _
  exact exists_congr (fun ψ => and_congr (existentialPrefix_delta_iff ψ) Iff.rfl)

theorem levyPi_one_iff {n : ℕ} (φ : ForcingFormulas.Formula n) :
    LevyPi 1 φ ↔ ∃ ψ, IsPiOne ψ ∧ ZFCFormulaEquivalent φ ψ := by
  change (∃ ψ, UniversalPrefix IsDeltaZero ψ ∧ ZFCFormulaEquivalent φ ψ) ↔ _
  exact exists_congr (fun ψ => and_congr (universalPrefix_delta_iff ψ) Iff.rfl)

end PolishSpaceBook.SetTheoryModels
