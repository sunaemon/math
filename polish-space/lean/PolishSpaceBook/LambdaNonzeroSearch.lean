module

public import PolishSpaceBook.LambdaOracleSearch

@[expose] public section

/-! # Exact domain of search for a nonzero input digit -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Zero input digits fail the search test; positive digits succeed. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For detecting a nonzero digit, reverse the numerical answers of the test and put
    $$H:=\lambdaab{a}{\lambdaab{b}{\lambdaab{k}{
    \LambdaZeroTest\,(ak)\,\ChurchNumeral{1}\,\ChurchNumeral{0}}}},
    \qquad \LambdaNonzeroSearch:=\LambdaSearchProgram{H}.$$
    The coordinate argument $b$ is unused. Three beta steps, one query, and zero testing give
    $$\LambdaInputSteps{p}{H\,o\,\ChurchNumeral{n}\,\ChurchNumeral{k}}{
    \begin{cases}
    \ChurchNumeral{1},&p(k)=0,\\
    \ChurchNumeral{0},&p(k)\ne0.
    \end{cases}}$$
-/
def inputNonzeroTest : AlphaTerm :=
  lam 11 (lam 3 (lam 4
    (app (app (app zeroTestTerm (app (var 11) (var 4))) (numeral 1)) (numeral 0))))

@[simp] theorem inputNonzeroTest_closed : inputNonzeroTest.Closed := by
  unfold inputNonzeroTest Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [zeroTestTerm_closed, numeral_closed, numeral_closed]
  decide

theorem inputNonzeroTest_apply (p : ℕ → ℕ) (n k : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app inputNonzeroTest (var 0)) (numeral n)) (numeral k))
      (numeral (if p k = 0 then 1 else 0)) := by
  let B (a b : AlphaTerm) :=
    app (app (app zeroTestTerm (app a b)) (numeral 1)) (numeral 0)
  have h₁ : Beta (app inputNonzeroTest (var 0))
      (lam 3 (lam 4 (B (var 0) (var 4)))) := by
    exact Beta.contract 11 (lam 3 (lam 4 (B (var 11) (var 4)))) (var 0)
  have h₂ : Beta (app (lam 3 (lam 4 (B (var 0) (var 4)))) (numeral n))
      (lam 4 (B (var 0) (var 4))) := by
    convert Beta.contract 3 (lam 4 (B (var 0) (var 4))) (numeral n) using 1
    rw [subst_lam_fresh _ _ 4 3 (by decide) (by rw [numeral_closed]; simp)]
    simp [B, subst_app, subst_var, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed 1), subst_closed _ _ _ (numeral_closed 0)]
  have h₃ : Beta (app (lam 4 (B (var 0) (var 4))) (numeral k))
      (B (var 0) (numeral k)) := by
    convert Beta.contract 4 (B (var 0) (var 4)) (numeral k) using 1
    simp [B, subst_app, subst_var, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed 1), subst_closed _ _ _ (numeral_closed 0)]
  have hb : Relation.ReflTransGen (OracleStep p)
      (app (app (app inputNonzeroTest (var 0)) (numeral n)) (numeral k))
      (B (var 0) (numeral k)) :=
    .tail (.tail (.single (.beta (.app_left _ (.app_left _ h₁))))
      (.beta (.app_left _ h₂))) (.beta h₃)
  have hs : Relation.ReflTransGen (OracleStep p)
      (app (app (app inputNonzeroTest (var 0)) (numeral n)) (numeral k))
      (app (app (app zeroTestTerm (numeral (p k))) (numeral 1)) (numeral 0)) :=
    hb.trans
      (oracle_steps_app_left (oracle_steps_app_left
        (oracle_steps_app_right zeroTestTerm (.single (.query k))) _) _)
  apply hs.trans
  cases p k with
  | zero =>
    simp only [ite_true]
    exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | succ r =>
    simp only [Nat.succ_ne_zero, ite_false]
    exact beta_steps_oracle (branch_succ r _ _)

/-- Return the first nonzero coordinate, ignoring the output-coordinate argument. -/
def nonzeroSearchProgram : AlphaTerm := searchProgram inputNonzeroTest

@[simp] theorem nonzeroSearchProgram_closed : nonzeroSearchProgram.Closed :=
  searchProgram_closed inputNonzeroTest_closed

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    If $j$ is the first nonzero coordinate, the displayed test returns a positive numeral before $j$ and zero at $j$. The sequential-search theorem therefore gives output $\ChurchNumeral{j}$. Closedness follows from the definitions.
-/
theorem nonzeroSearchProgram_hit {p : ℕ → ℕ} (n j : ℕ)
    (hj : p j ≠ 0) (hbefore : ∀ k < j, p k = 0) :
    OracleRuns p nonzeroSearchProgram n j := by
  apply searchProgram_hit inputNonzeroTest_closed n j
  · simpa only [hj, ite_false] using inputNonzeroTest_apply p n j
  · intro k hk
    exact ⟨0, by simpa only [hbefore k hk, ite_true] using inputNonzeroTest_apply p n k⟩

/-- Finite use and output uniqueness exclude every numerical output on the zero name. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Suppose now that $p(k)=0$ for every $k$, but the program produces $\ChurchNumeral{m}$. By the finite-use argument in §{sec:lambda-input-finite-use}, some $N$ bounds every queried coordinate in this finite reduction. Set $j:=\max\{N,m+1\}$ and define
    $$q(k):=\begin{cases}1,&k=j,\\p(k),&k\ne j.\end{cases}$$
    Since $q$ agrees with $p$ below $N$, the same reduction with input $q$ produces $\ChurchNumeral{m}$. However, the first nonzero coordinate of $q$ is $j$, so the preceding calculation also gives $\ChurchNumeral{j}$. Uniqueness of numeral outputs forces $m=j$, contradicting $j>m$. Thus the all-zero name admits no numeral output.
-/
theorem nonzeroSearchProgram_no_output {p : ℕ → ℕ} (hp : ∀ k, p k = 0) (n m : ℕ) :
    ¬ OracleRuns p nonzeroSearchProgram n m := by
  intro h
  obtain ⟨N, hN⟩ := h.finite_use
  let j := max N (m + 1)
  let q : ℕ → ℕ := fun k => if k = j then 1 else p k
  have hq : OracleRuns q nonzeroSearchProgram n m := hN q (by
    intro i hi
    have hij : i ≠ j := by dsimp [j]; omega
    simp [q, hij])
  have hj : OracleRuns q nonzeroSearchProgram n j := nonzeroSearchProgram_hit n j
    (by simp [q]) (by
      intro k hk
      have hkj : k ≠ j := by omega
      simp [q, hkj, hp])
  have he := hq.output_unique hj
  dsimp [j] at he
  omega

/-- An exact graph theorem, including names with no successful candidate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Exact domain of nonzero search
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Any name admitting a numeral output therefore has a first nonzero coordinate. The successful-search calculation and output uniqueness identify that coordinate with the output. This proves both directions of the equivalence, including when the first nonzero coordinate is zero.
-/
theorem nonzeroSearchProgram_runs_iff (p : ℕ → ℕ) (n m : ℕ) :
    OracleRuns p nonzeroSearchProgram n m ↔ p m ≠ 0 ∧ ∀ k < m, p k = 0 := by
  classical
  constructor
  · intro h
    have hex : ∃ j, p j ≠ 0 := by
      by_contra! hz
      exact nonzeroSearchProgram_no_output hz n m h
    have hj := nonzeroSearchProgram_hit n (Nat.find hex) (Nat.find_spec hex)
      (fun k hk => by simpa using Nat.find_min hex hk)
    have he := h.output_unique hj
    subst m
    exact ⟨Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
  · rintro ⟨hm, hb⟩
    exact nonzeroSearchProgram_hit n m hm hb

theorem nonzeroSearchProgram_domain (p : ℕ → ℕ) (n : ℕ) :
    (∃ m, OracleRuns p nonzeroSearchProgram n m) ↔ ∃ k, p k ≠ 0 := by
  classical
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, ((nonzeroSearchProgram_runs_iff p n m).mp hm).1⟩
  · intro hex
    exact ⟨Nat.find hex, nonzeroSearchProgram_hit n (Nat.find hex) (Nat.find_spec hex)
      (fun k hk => by simpa using Nat.find_min hex hk)⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
