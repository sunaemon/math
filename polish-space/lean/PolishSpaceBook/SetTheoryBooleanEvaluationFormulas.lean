module

public import PolishSpaceBook.SetTheoryBooleanEvaluation
public import PolishSpaceBook.SetTheoryInternalOrderMinima
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # Internal formulas for Boolean evaluation

The partial-assignment predicate is bounded. Its existential closure is used
with Separation on the node set to collect the largest internal partial
assignment, without assuming that the model contains all external subsets.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.BooleanEvaluation
open FirstOrder Language ZFSet ForcingFormulas
open scoped Classical
universe u

def trueChildPredicate {n : ℕ} (T R E s : Fin n) : BoundedSetPredicate n :=
  .ex T (.conj (.pairMember R.castSucc (Fin.last n) s.castSucc)
    (.member (Fin.last n) E.castSucc))

def trueChildFormula {n : ℕ} (T R E s : Fin n) : ForcingFormulas.Formula n :=
  (trueChildPredicate T R E s).compile

lemma realize_trueChildFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (T R E s : Fin n) (xs : Fin n → M) :
    (trueChildFormula T R E s).Realize Empty.elim xs ↔
      ∃ t ∈ (xs T).val, pair t (xs s).val ∈ (xs R).val ∧ t ∈ (xs E).val := by
  rw [trueChildFormula, BoundedSetPredicate.realize_compile hM]
  simp only [trueChildPredicate, BoundedSetPredicate.eval, Fin.snoc_last, Fin.snoc_castSucc,
    Function.comp_apply]

def stepPredicate {n : ℕ} (T R U C L E s : Fin n) : BoundedSetPredicate n :=
  .disj (.conj (.member s U) (trueChildPredicate T R E s))
    (.conj (.neg (.member s U))
      (.disj (.conj (.member s C) (.neg (trueChildPredicate T R E s)))
        (.conj (.neg (.member s C)) (.member s L))))

lemma eval_stepPredicate {n : ℕ} (T R U C L E s : Fin n) (xs : Fin n → ZFSet.{u}) :
    (stepPredicate T R U C L E s).eval xs ↔
      Step (xs T) (xs R) (xs U) (xs C) (xs L) (xs E) (xs s) := by
  simp only [stepPredicate, trueChildPredicate, BoundedSetPredicate.eval,
    Fin.snoc_last, Fin.snoc_castSucc]
  unfold Step
  split_ifs <;> simp_all

def stepFormula {n : ℕ} (T R U C L E s : Fin n) : ForcingFormulas.Formula n :=
  (stepPredicate T R U C L E s).compile

lemma realize_stepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (T R U C L E s : Fin n) (xs : Fin n → M) :
    (stepFormula T R U C L E s).Realize Empty.elim xs ↔
      Step (xs T).val (xs R).val (xs U).val (xs C).val (xs L).val (xs E).val (xs s).val := by
  exact ((stepPredicate T R U C L E s).realize_compile hM xs).trans
    (eval_stepPredicate T R U C L E s (Subtype.val ∘ xs))

def closedDomainPredicate {n : ℕ} (T R D : Fin n) : BoundedSetPredicate n :=
  .all D (.all T.castSucc
    (.disj (.neg (.pairMember R.castSucc.castSucc (Fin.last (n + 1)) (Fin.last n).castSucc))
      (.member (Fin.last (n + 1)) D.castSucc.castSucc)))

lemma eval_closedDomainPredicate {n : ℕ} (T R D : Fin n) (xs : Fin n → ZFSet.{u}) :
    (closedDomainPredicate T R D).eval xs ↔
      ∀ s ∈ xs D, ∀ t ∈ xs T, pair t s ∈ xs R → t ∈ xs D := by
  simp only [closedDomainPredicate, BoundedSetPredicate.eval, Fin.snoc_last, Fin.snoc_castSucc,
    or_iff_not_imp_left, not_not]

def closedDomainFormula {n : ℕ} (T R D : Fin n) : ForcingFormulas.Formula n :=
  (closedDomainPredicate T R D).compile

lemma realize_closedDomainFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (T R D : Fin n) (xs : Fin n → M) :
    (closedDomainFormula T R D).Realize Empty.elim xs ↔
      ∀ s ∈ (xs D).val, ∀ t ∈ (xs T).val, pair t s ∈ (xs R).val → t ∈ (xs D).val := by
  exact ((closedDomainPredicate T R D).realize_compile hM xs).trans
    (eval_closedDomainPredicate T R D (Subtype.val ∘ xs))

def partialPredicate {n : ℕ} (T R U C L D E : Fin n) : BoundedSetPredicate n :=
  .conj (.subset D T) (.conj (.subset E D) (.conj (closedDomainPredicate T R D)
    (.all D (.iff (.member (Fin.last n) E.castSucc)
      (stepPredicate T.castSucc R.castSucc U.castSucc C.castSucc L.castSucc E.castSucc (Fin.last n))))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    A partial evaluation consists of a domain $D$ and its true-node set $E$, satisfying the formula
    $$\begin{aligned}
    \sigma(D,E)\;:\equiv\;&D\IncludedIn T\land E\IncludedIn D\\
    &{}\land\forall s\in D\;\forall t\in T\;
     (\langle t,s\rangle\in R\longrightarrow t\in D)\\
    &{}\land\forall s\in D\;(s\in E\longleftrightarrow\theta(E,s)).
    \end{aligned}$$
    The parameters $T,R,U,C,L$ are suppressed in this notation.
-/
def partialFormula {n : ℕ} (T R U C L D E : Fin n) : ForcingFormulas.Formula n :=
  (partialPredicate T R U C L D E).compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Thus, for parameters and candidate sets in a
    transitive model, its internal interpretation recognizes exactly the actual partial evaluations.
-/
lemma realize_partialFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (T R U C L D E : Fin n) (xs : Fin n → M) :
    (partialFormula T R U C L D E).Realize Empty.elim xs ↔
      Partial (xs T).val (xs R).val (xs U).val (xs C).val (xs L).val (xs D).val (xs E).val := by
  rw [partialFormula, BoundedSetPredicate.realize_compile hM]
  simp only [partialPredicate, BoundedSetPredicate.eval, eval_closedDomainPredicate,
    eval_stepPredicate, Fin.snoc_last, Fin.snoc_castSucc, Function.comp_apply, Partial]

lemma trueChildFormula_deltaZero {n : ℕ} (T R E s : Fin n) :
    IsDeltaZero (trueChildFormula T R E s) :=
  (trueChildPredicate T R E s).compile_deltaZero

lemma stepFormula_deltaZero {n : ℕ} (T R U C L E s : Fin n) :
    IsDeltaZero (stepFormula T R U C L E s) :=
  (stepPredicate T R U C L E s).compile_deltaZero

lemma closedDomainFormula_deltaZero {n : ℕ} (T R D : Fin n) :
    IsDeltaZero (closedDomainFormula T R D) :=
  (closedDomainPredicate T R D).compile_deltaZero

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Expanding the subset and ordered-pair clauses
    as in §{sec:zfc-absoluteness} makes $\sigma$ a bounded formula.
-/
lemma partialFormula_deltaZero {n : ℕ} (T R U C L D E : Fin n) :
    IsDeltaZero (partialFormula T R U C L D E) :=
  (partialPredicate T R U C L D E).compile_deltaZero

/-- Parameters T,R,U,C,L, input s, and two quantified sets D,E. -/
def collectedFormula (truth : Bool) : ForcingFormulas.Formula 6 :=
  (partialFormula (0 : Fin 8) 1 2 3 4 6 7 ⊓ memberAt 5 (if truth then 7 else 6)).ex.ex

lemma realize_collectedFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (truth : Bool) (T R U C L s : M) :
    (collectedFormula truth).Realize Empty.elim ![T, R, U, C, L, s] ↔
      ∃ D E : M, Partial T.val R.val U.val C.val L.val D.val E.val ∧
        s.val ∈ (if truth then E.val else D.val) := by
  cases truth <;>
    simp [collectedFormula, realize_partialFormula hM]

end PolishSpaceBook.SetTheoryModels.BooleanEvaluation
