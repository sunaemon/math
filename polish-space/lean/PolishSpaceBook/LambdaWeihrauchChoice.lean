module

public import PolishSpaceBook.ComputablePolishSpacesTTE
public import PolishSpaceBook.LambdaNumericalProjections
public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # A closed-lambda reduction from LPO to natural-number closed choice

Negative names enumerate exclusions, with zero denoting an empty stage.
Both translators are explicit terms of the book's beta/query calculus.
-/
namespace PolishSpaceBook.WeihrauchChoice
open NamedLambda NamedLambda.AlphaTerm

/-- The naturals not excluded by a negative name. -/

def allowedNaturals (a : baire_space) : Set ℕ := {m | ∀ s, a s ≠ m + 1}

/-- Natural numbers are named by their zeroth coordinate. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The output natural number uses $\delta_{\NN}$. The problem
    \termdefine{closed choice on the natural numbers}, denoted by $\ClosedChoiceNaturals$, takes a negative name $a$
    with $\NaturalChoiceSet{a}\ne\emptyset$ and permits any output in $\NaturalChoiceSet{a}$, again named by
    $\delta_{\NN}$.
-/
def closedChoice : NameProblem := fun a => {q | q 0 ∈ allowedNaturals a}

/-- LPO returns zero exactly on the all-zero input name. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The \termdefine{limited principle of omniscience problem} $\LimitedOmniscienceProblem$ asks whether an input name
    has a nonzero coordinate:
    $$\LimitedOmniscienceProblem(p)=
    \begin{cases}
    0,&\forall k\in\NN,\ p(k)=0,\\
    1,&\exists k\in\NN,\ p(k)\ne0.
    \end{cases}$$
-/
def lpo : NameProblem := fun p =>
  {q | (q 0 = 0 ∧ ∀ k, p k = 0) ∨ (q 0 = 1 ∧ ∃ k, p k ≠ 0)}

/-- Two rows exclude positive candidates and the zero candidate, respectively. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    \emph{Preprocessing.} Decode a stage as $s=\NatPair{t}{k}$ and define the negative name $K(p)$ by
    $$K(p)(\NatPair{t}{k})=
    \begin{cases}
    k+2,&t=0\text{ and }p(k)=0,\\
    1,&t=1\text{ and }p(k)\ne0,\\
    0,&\text{otherwise}.
    \end{cases}$$
-/
def preprocess (p : baire_space) (s : ℕ) : ℕ :=
  let t := s.unpair.1
  let k := s.unpair.2
  if t = 0 then if p k = 0 then k + 2 else 0
  else if t = 1 then if p k = 0 then 0 else 1
  else 0

/-- A positive chosen witness means that a nonzero input coordinate exists. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Define a constant output name by
    $$H(q)(n):=\begin{cases}0,&q(0)=0,\\1,&q(0)\ne0.\end{cases}$$
-/
def postprocess (q : baire_space) : baire_space := fun _ => if q 0 = 0 then 0 else 1

@[simp] theorem preprocess_row_zero (p : baire_space) (k : ℕ) :
    preprocess p (Nat.pair 0 k) = if p k = 0 then k + 2 else 0 := by
  simp [preprocess, Nat.unpair_pair]

@[simp] theorem preprocess_row_one (p : baire_space) (k : ℕ) :
    preprocess p (Nat.pair 1 k) = if p k = 0 then 0 else 1 := by
  simp [preprocess, Nat.unpair_pair]

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The two rows have different jobs. Row $0$ excludes $k+1$ exactly when $p(k)=0$.
    Row $1$ excludes $0$ as soon as any nonzero input coordinate is found. Hence
    $$\NaturalChoiceSet{K(p)}=
    \begin{cases}
    \{0\},&\forall k\in\NN,\ p(k)=0,\\
    \{k+1:k\in\NN,\ p(k)\ne0\},&\exists k\in\NN,\ p(k)\ne0.
    \end{cases}$$
-/
theorem zero_allowed_iff (p : baire_space) :
    0 ∈ allowedNaturals (preprocess p) ↔ ∀ k, p k = 0 := by
  change (∀ s, preprocess p s ≠ 1) ↔ _
  constructor
  · intro h k
    by_contra hk
    exact h (Nat.pair 1 k) (by simp [hk])
  · intro h s
    simp only [preprocess, h, ↓reduceIte]
    split_ifs <;> omega

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Indeed, only the $t=1$ row can exclude $0$, and only the stage $\NatPair{0}{k}$ can exclude $k+1$.
-/
theorem succ_allowed_iff (p : baire_space) (k : ℕ) :
    k + 1 ∈ allowedNaturals (preprocess p) ↔ p k ≠ 0 := by
  change (∀ s, preprocess p s ≠ k + 1 + 1) ↔ _
  constructor
  · intro h hk
    exact h (Nat.pair 0 k) (by simp [hk])
  · intro hk s
    by_cases ht : s.unpair.1 = 0
    · by_cases hp : p s.unpair.2 = 0
      · have hn : s.unpair.2 ≠ k := by
          intro he
          exact hk (he ▸ hp)
        simp only [preprocess, ht, ↓reduceIte, hp]
        omega
      · simp [preprocess, ht, hp]
    · by_cases ht' : s.unpair.1 = 1
      · by_cases hp : p s.unpair.2 = 0 <;> simp [preprocess, ht', hp]
      · simp [preprocess, ht, ht']

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The displayed set is nonempty in both cases. Thus $K$ always supplies a valid instance of $\ClosedChoiceNaturals$
    without first deciding which case holds.
-/
theorem choice_input_nonempty (p : baire_space) : (closedChoice (preprocess p)).Nonempty := by
  classical
  by_cases h : ∀ k, p k = 0
  · exact ⟨fun _ => 0, (zero_allowed_iff p).mpr h⟩
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact ⟨fun _ => k + 1, (succ_allowed_iff p k).mpr hk⟩

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    If $m=0$, every coordinate of $p$ is zero. If $m>0$, write $m=k+1$; then $p(k)\ne0$.
    Consequently $\delta_{\NN}(H(q))=\LimitedOmniscienceProblem(p)$ for every permitted choice returned by $\Gamma$.
    The postprocessor uses only the oracle's answer, so this is a strong reduction.
-/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The preprocessor can enumerate an exclusion once a finite query justifies it. It does not choose a member of
    $\NaturalChoiceSet{K(p)}$. That choice is precisely what the oracle supplies. The postprocessor then reads the
    answer
    without using the original input, illustrating the additional restriction in a strong reduction.
-/
theorem postprocess_correct (p q : baire_space) (hq : q ∈ closedChoice (preprocess p)) :
    postprocess q ∈ lpo p := by
  change (postprocess q 0 = 0 ∧ ∀ k, p k = 0) ∨
    (postprocess q 0 = 1 ∧ ∃ k, p k ≠ 0)
  by_cases h : q 0 = 0
  · left
    refine ⟨by simp [postprocess, h], (zero_allowed_iff p).mp ?_⟩
    simpa only [closedChoice, Set.mem_ofPred_eq, h] using hq
  · right
    refine ⟨by simp [postprocess, h], ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    exact ⟨k, (succ_allowed_iff p k).mp (by
      simpa only [closedChoice, Set.mem_ofPred_eq, hk, Nat.succ_eq_add_one] using hq)⟩

/-- This is an abbreviation in lambda syntax, not an additional reduction rule. -/
def zeroCase (C A B : AlphaTerm) : AlphaTerm := app (app (app zeroTestTerm C) A) B

theorem zeroCase_fv (C A B : AlphaTerm) :
    (zeroCase C A B).fv = C.fv ∪ A.fv ∪ B.fv := by
  simp only [zeroCase, fv_app]
  rw [zeroTestTerm_closed]
  simp only [Finset.empty_union]

theorem zeroCase_subst (C A B R : AlphaTerm) (x : ℕ) :
    (zeroCase C A B).subst x R = zeroCase (C.subst x R) (A.subst x R) (B.subst x R) := by
  simp only [zeroCase, subst_app, subst_closed _ _ _ zeroTestTerm_closed]

theorem zeroCase_steps {p : baire_space} {C A B : AlphaTerm} {c a b : ℕ}
    (hc : Relation.ReflTransGen (OracleStep p) C (numeral c))
    (ha : Relation.ReflTransGen (OracleStep p) A (numeral a))
    (hb : Relation.ReflTransGen (OracleStep p) B (numeral b)) :
    Relation.ReflTransGen (OracleStep p) (zeroCase C A B)
      (numeral (if c = 0 then a else b)) := by
  apply (oracle_steps_app (oracle_steps_app (oracle_steps_app_right zeroTestTerm hc) ha) hb).trans
  cases c with
  | zero => exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | succ c => exact beta_steps_oracle (branch_succ c _ _)

/-- Expand the two numerical projections and the two row computations. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: proof
  excerpt: |
    \emph{Closed lambda programs.} The numerical projections, equality test, addition, and zero test are the
    closed terms of §{sec:lambda-basic-data}. For variables $o,z$, abbreviate
    $$\begin{aligned}
    \LambdaTermName{tag}(z)&:=\LambdaNumericProjection{1}\,z,& \LambdaTermName{index}(z)&:=\LambdaNumericProjection{2}\,z,\\
    \LambdaTermName{rowZero}(o,z)&:= \LambdaZeroTest\,(o( \LambdaTermName{index}(z)))\,( \LambdaAdd\,
    \LambdaTermName{index}(z)\, \ChurchNumeral{2})\, \ChurchNumeral{0},\\
    \LambdaTermName{rowOne}(o,z)&:=\LambdaZeroTest\,(o(\LambdaTermName{index}(z)))\,\ChurchNumeral{0}\,\ChurchNumeral{1}.
    \end{aligned}$$
-/
def preBody (O S : AlphaTerm) : AlphaTerm :=
  let T := app (numericalProjectionTerm true) S
  let I := app (numericalProjectionTerm false) S
  let Q := app O I
  let E₀ := zeroCase Q (app (app additionTerm I) (numeral 2)) (numeral 0)
  let E₁ := zeroCase Q (numeral 0) (numeral 1)
  zeroCase T E₀ (zeroCase (app (app equalityTerm T) (numeral 1)) (numeral 0) E₁)

theorem preBody_fv (O S : AlphaTerm) : (preBody O S).fv = O.fv ∪ S.fv := by
  simp only [preBody, zeroCase_fv, fv_app]
  rw [numericalProjectionTerm_closed true, numericalProjectionTerm_closed false,
    additionTerm_closed, equalityTerm_closed, numeral_closed 0, numeral_closed 1, numeral_closed 2]
  simp only [Finset.empty_union, Finset.union_empty]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem preBody_subst (O S R : AlphaTerm) (x : ℕ) :
    (preBody O S).subst x R = preBody (O.subst x R) (S.subst x R) := by
  simp only [preBody, zeroCase_subst, subst_app,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false),
    subst_closed _ _ _ additionTerm_closed, subst_closed _ _ _ equalityTerm_closed,
    subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1),
    subst_closed _ _ _ (numeral_closed 2)]

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Now put
    $$\begin{aligned}
    \LambdaTermName{prepareChoice}&:=\lambdaab{o}{\lambdaab{z}{
    \LambdaZeroTest\,\LambdaTermName{tag}(z)\,\LambdaTermName{rowZero}(o,z)\,
    \bigl(\LambdaZeroTest\,(\LambdaEqual\,\LambdaTermName{tag}(z)\,\ChurchNumeral{1})\,
    \ChurchNumeral{0}\,\LambdaTermName{rowOne}(o,z)\bigr)}},\\
    \LambdaTermName{readChoice}&:=\lambdaab{o}{\lambdaab{z}{
    \LambdaZeroTest\,(o\ChurchNumeral{0})\,\ChurchNumeral{0}\,\ChurchNumeral{1}}}.
    \end{aligned}$$
-/
def preProgram : AlphaTerm := lam 1 (lam 2 (preBody (var 1) (var 2)))

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Expand $\LambdaTermName{tag}, \LambdaTermName{index}, \LambdaTermName{rowZero}, \LambdaTermName{rowOne}$ inside
    these abstractions. The numerical routines are closed, and all remaining variables are
    bound, so $\LambdaTermName{prepareChoice}$ and $\LambdaTermName{readChoice}$ are closed lambda terms.
-/
@[simp] theorem preProgram_closed : preProgram.Closed := by
  unfold Closed preProgram
  rw [fv_lam, fv_lam, preBody_fv]
  change ((({1} : Finset ℕ) ∪ {2}).erase 2).erase 1 = ∅
  decide

theorem preProgram_start (p : baire_space) (s : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app preProgram (var 0)) (numeral s)) (preBody (var 0) (numeral s)) := by
  have h₁ : Beta (app preProgram (var 0)) (lam 2 (preBody (var 0) (var 2))) := by
    exact Beta.contract 1 (lam 2 (preBody (var 1) (var 2))) (var 0)
  have h₂ : Beta (app (lam 2 (preBody (var 0) (var 2))) (numeral s))
      (preBody (var 0) (numeral s)) := by
    convert Beta.contract 2 (preBody (var 0) (var 2)) (numeral s) using 1
    simp [preBody_subst, subst_var]
  exact .tail (.single (.beta (.app_left _ h₁))) (.beta h₂)

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Two outer beta steps expose each program body. On input $\ChurchNumeral{s}$ with $s= \NatPair{t}{k}$, the
    numerical projections reduce
    to $\ChurchNumeral{t}$ and $\ChurchNumeral{k}$, and the query to $o( \LambdaTermName{index}(
    \ChurchNumeral{s}))$ returns $\ChurchNumeral{p(k)}$.
    Zero testing then gives the stated values of $\LambdaTermName{rowZero}$ and $\LambdaTermName{rowOne}$. The outer
    test selects row $0$ when $t=0$;
    otherwise equality testing selects row $1$ exactly when $t=1$, and every other row returns zero.
-/
theorem preProgram_runs (p : baire_space) (s : ℕ) :
    OracleRuns p preProgram s (preprocess p s) := by
  have ht : Relation.ReflTransGen (OracleStep p)
      (app (numericalProjectionTerm true) (numeral s)) (numeral s.unpair.1) :=
    beta_steps_oracle (numericalProjectionTerm_apply true s)
  have hi : Relation.ReflTransGen (OracleStep p)
      (app (numericalProjectionTerm false) (numeral s)) (numeral s.unpair.2) :=
    beta_steps_oracle (numericalProjectionTerm_apply false s)
  have hq := (oracle_steps_app_right (var 0) hi).tail (.query s.unpair.2)
  have ha := (oracle_steps_app_left (oracle_steps_app_right additionTerm hi) (numeral 2)).trans
    (beta_steps_oracle (additionTerm_apply s.unpair.2 2))
  have he := (oracle_steps_app_left (oracle_steps_app_right equalityTerm ht) (numeral 1)).trans
    (beta_steps_oracle (equalityTerm_apply s.unpair.1 1))
  have hzero := zeroCase_steps hq ha (.refl (a := numeral 0))
  have hone := zeroCase_steps hq (.refl (a := numeral 0)) (.refl (a := numeral 1))
  have hother := zeroCase_steps he (.refl (a := numeral 0)) hone
  have hbody := zeroCase_steps ht hzero hother
  apply (preProgram_start p s).trans
  by_cases h : s.unpair.1 = 1
  · simpa only [preBody, preprocess, h, ↓reduceIte, zero_ne_one, one_ne_zero] using hbody
  · simpa only [preBody, preprocess, h, ↓reduceIte, zero_ne_one, one_ne_zero] using hbody

def postBody (O : AlphaTerm) : AlphaTerm :=
  zeroCase (app O (numeral 0)) (numeral 0) (numeral 1)

theorem postBody_fv (O : AlphaTerm) : (postBody O).fv = O.fv := by
  simp only [postBody, zeroCase_fv, fv_app]
  rw [numeral_closed 0, numeral_closed 1]
  simp only [Finset.union_empty]

theorem postBody_subst (O R : AlphaTerm) (x : ℕ) :
    (postBody O).subst x R = postBody (O.subst x R) := by
  simp only [postBody, zeroCase_subst, subst_app,
    subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1)]

def postProgram : AlphaTerm := lam 1 (lam 2 (postBody (var 1)))

@[simp] theorem postProgram_closed : postProgram.Closed := by
  unfold Closed postProgram
  rw [fv_lam, fv_lam, postBody_fv]
  simp [fv_var]

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    For $\LambdaTermName{readChoice}$, the single query returns $\ChurchNumeral{q(0)}$, whose zero test returns the
    required bit. Thus
    $$\LambdaInputSteps{p}{\LambdaTermName{prepareChoice}\,o\,\ChurchNumeral{s}}{\ChurchNumeral{K(p)(s)}},\qquad
    \LambdaInputSteps{q}{\LambdaTermName{readChoice}\,o\,\ChurchNumeral{n}}{\ChurchNumeral{H(q)(n)}}.$$
-/
theorem postProgram_runs (p : baire_space) (n : ℕ) :
    OracleRuns p postProgram n (postprocess p n) := by
  have h₁ : Beta (app postProgram (var 0)) (lam 2 (postBody (var 0))) := by
    exact Beta.contract 1 (lam 2 (postBody (var 1))) (var 0)
  have h₂ : Beta (app (lam 2 (postBody (var 0))) (numeral n)) (postBody (var 0)) := by
    convert Beta.contract 2 (postBody (var 0)) (numeral n) using 1
    simp [postBody_subst, subst_var]
  apply (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
  exact zeroCase_steps (.single (.query 0)) (.refl (a := numeral 0)) (.refl (a := numeral 1))

/-- Lambda computation on the declared domain; no assertion is made off that domain. -/
def LambdaComputable (F : PartialNameMap) : Prop :=
  ∃ P : AlphaTerm, P.Closed ∧ ∀ p q, F p = some q →
    ∀ n m, OracleRuns p P n m ↔ q n = m

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: proof
  excerpt: |
    All these derivations are finite for arbitrary input names; the names need not themselves be computable.
    Numerical-output uniqueness proves that these terms realize exactly the two specified operators.
    \end{proof}
-/
theorem preprocess_computable : LambdaComputable (fun p => some (preprocess p)) := by
  refine ⟨preProgram, preProgram_closed, ?_⟩
  intro p q h n m
  have hq : preprocess p = q := Option.some.inj h
  subst q
  exact (typeTwoComputes_iff_runs.mpr
    ⟨preProgram_closed, fun (p : (Set.univ : Set baire_space)) n => preProgram_runs p.val n⟩).2
      ⟨p, Set.mem_univ p⟩ n m

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: proof
  excerpt: |
    All these derivations are finite for arbitrary input names; the names need not themselves be computable.
    Numerical-output uniqueness proves that these terms realize exactly the two specified operators.
    \end{proof}
-/
theorem postprocess_computable : LambdaComputable (fun p => some (postprocess p)) := by
  refine ⟨postProgram, postProgram_closed, ?_⟩
  intro p q h n m
  have hq : postprocess p = q := Option.some.inj h
  subst q
  exact (typeTwoComputes_iff_runs.mpr
    ⟨postProgram_closed, fun (p : (Set.univ : Set baire_space)) n => postProgram_runs p.val n⟩).2
      ⟨p, Set.mem_univ p⟩ n m

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: statement
  kind: theorem
  title: A concrete strong Weihrauch reduction
-/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: proof
  excerpt: |
    \emph{One oracle call and postprocessing.} Let $\Gamma$ be any realizer of $\ClosedChoiceNaturals$ and put
    $q:=\Gamma(K(p))$. The natural number $m:=q(0)$ belongs to $\NaturalChoiceSet{K(p)}$.
-/
theorem lpo_strongly_reduces_to_closedChoice :
    StrongWeihrauchReduces LambdaComputable lpo closedChoice := by
  refine ⟨fun p => some (preprocess p), fun p => some (postprocess p),
    preprocess_computable, postprocess_computable, ?_⟩
  intro Γ hΓ p _
  obtain ⟨q, hq, hmem⟩ := hΓ (preprocess p) (choice_input_nonempty p)
  refine ⟨postprocess q, ?_, postprocess_correct p q hmem⟩
  simp [strongWeihrauchPostprocess, hq]


theorem allowedNaturals_closed (a : baire_space) : IsClosed (allowedNaturals a) :=
  isClosed_discrete _

theorem lpo_domain_nonempty (p : baire_space) : (lpo p).Nonempty := by
  classical
  by_cases h : ∀ k, p k = 0
  · exact ⟨fun _ => 0, Or.inl ⟨rfl, h⟩⟩
  · push Not at h
    exact ⟨fun _ => 1, Or.inr ⟨rfl, h⟩⟩

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: statement
  kind: lemma
  title: No computable LPO realizer
-/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Suppose a closed lambda program realizes $\LimitedOmniscienceProblem$. On the all-zero input name, its computation
    of output coordinate $0$ returns $\ChurchNumeral{0}$. Finite use in §{sec:type-two-lambda-continuity} gives a bound
    $N$ such that every input agreeing at coordinates $i<N$ admits the same reduction to $\ChurchNumeral{0}$.
    Change only coordinate $N$ to $1$. This new input still admits that reduction, but its required output coordinate
    is $1$. The realizer must therefore also return $\ChurchNumeral{1}$, contradicting uniqueness of numerical outputs.
    \end{proof}
-/
theorem no_lambda_lpo_realizer (Φ : PartialNameMap) (hΦ : LambdaComputable Φ) :
    ¬ lpo.IsRealizer Φ := by
  classical
  obtain ⟨P, _, hP⟩ := hΦ
  intro hreal
  let z : baire_space := fun _ => 0
  obtain ⟨q, hq, hqmem⟩ := hreal z (lpo_domain_nonempty z)
  have hqzero : q 0 = 0 := by
    simpa [lpo, z] using hqmem
  have hrun : OracleRuns z P 0 0 := (hP z q hq 0 0).mpr hqzero
  obtain ⟨N, hN⟩ := hrun.finite_use
  let p : baire_space := fun i => if i = N then 1 else 0
  have hsame : OracleRuns p P 0 0 := hN p (by
    intro i hi
    simp [p, z, ne_of_lt hi])
  obtain ⟨r, hr, hrmem⟩ := hreal p (lpo_domain_nonempty p)
  have hrone : r 0 = 1 := by
    rcases hrmem with ⟨_, hall⟩ | ⟨hone, _⟩
    · have hbad := hall N
      simp [p] at hbad
    · exact hone
  have hother : OracleRuns p P 0 1 := (hP p r hr 0 1).mpr hrone
  exact Nat.zero_ne_one (hsame.output_unique hother)

end PolishSpaceBook.WeihrauchChoice
