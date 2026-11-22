module

public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # Sequential search by self-application in lambda calculus -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- The self argument is duplicated only in the continuation branch. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Self-application allows a finite term to continue testing candidates without a prescribed iteration bound. For a test term $G$, choose $s,k$ fresh for $G$ and put
    $$\LambdaSearchKernel{G}:=\lambdaab{s}{\lambdaab{k}{
    \LambdaZeroTest\,(Gk)\,k\,\bigl((ss)(\LambdaSucc\,k)\bigr)}}.$$
    The zero branch returns the current candidate; the positive branch applies the duplicated self argument to the next candidate. Define one closed \termdefine{lambda search term} by
    $$\LambdaSearch:=\lambdaab{g}{
    \bigl(\LambdaSearchKernel{g}\,\LambdaSearchKernel{g}\bigr)\ChurchNumeral{0}}.$$
    Expand both occurrences of the kernel before abstraction, keeping their binders distinct from $g$. These are finite lambda terms; no numerical bound is an argument of the search.
-/
def searchKernel (G : AlphaTerm) : AlphaTerm :=
  lam 3 (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (var 4))
    (app (app (var 3) (var 3)) (app successorTerm (var 4)))))

def searchFrom (G : AlphaTerm) (k : ℕ) : AlphaTerm :=
  app (app (searchKernel G) (searchKernel G)) (numeral k)

@[simp] theorem searchKernel_fv (G : AlphaTerm) :
    (searchKernel G).fv = (G.fv.erase 4).erase 3 := by
  ext x
  simp [searchKernel, fv_lam, fv_app, fv_var]
  tauto

theorem subst_searchKernel (G R : AlphaTerm) (x : ℕ) (hx3 : 3 ≠ x) (hx4 : 4 ≠ x)
    (hR3 : 3 ∉ R.fv) (hR4 : 4 ∉ R.fv) :
    subst (searchKernel G) x R = searchKernel (subst G x R) := by
  unfold searchKernel
  rw [subst_lam_fresh _ _ 3 x hx3 hR3, subst_lam_fresh _ _ 4 x hx4 hR4]
  simp [subst_app, subst_var, hx3, hx4,
    subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ successorTerm_closed]

/-- One finite closed term takes the test as an argument. -/
def searchTerm : AlphaTerm := lam 7 (searchFrom (var 7) 0)

@[simp] theorem searchTerm_closed : searchTerm.Closed := by
  unfold Closed searchTerm searchFrom
  rw [fv_lam, fv_app, fv_app, numeral_closed]
  simp [fv_var]

theorem searchTerm_start {G : AlphaTerm} (hG : G.fv ⊆ {0}) :
    Beta (app searchTerm G) (searchFrom G 0) := by
  convert Beta.contract 7 (searchFrom (var 7) 0) G using 1 <;> try rfl
  simp [searchFrom, subst_app, subst_searchKernel _ _ _ (by decide : 3 ≠ 7)
    (by decide : 4 ≠ 7) (input_fresh hG (by decide)) (input_fresh hG (by decide)),
    subst_var, subst_closed _ _ _ (numeral_closed 0)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Fix $p,n$ and abbreviate $G:=H\,o\,\ChurchNumeral{n}$ and $j:=j(p,n)$. The only possible free variable of $G$ is $o$. Choose the kernel binders different from $o$ and set
    $$S_k:=\bigl(\LambdaSearchKernel{G}\,\LambdaSearchKernel{G}\bigr)\ChurchNumeral{k}.$$
    The two outer beta steps of the wrapper, followed by the beta step of the search term, produce $S_0$. Two beta steps unfold the self-application at any candidate:
    $$S_k\to_\beta^*
    \LambdaZeroTest\,(G\ChurchNumeral{k})\,\ChurchNumeral{k}\,
    \bigl((\LambdaSearchKernel{G}\,\LambdaSearchKernel{G})(\LambdaSucc\,\ChurchNumeral{k})\bigr).$$
    Freshness of the binders preserves the test term and the duplicated kernel in these substitutions.
-/
theorem searchFrom_unfold {G : AlphaTerm} (hG : G.fv ⊆ {0}) (k : ℕ) :
    Relation.ReflTransGen Beta (searchFrom G k)
      (app (app (app zeroTestTerm (app G (numeral k))) (numeral k))
        (app (app (searchKernel G) (searchKernel G)) (app successorTerm (numeral k)))) := by
  have hf (x : ℕ) (hx : x ≠ 0) : x ∉ G.fv := input_fresh hG hx
  have hK : 4 ∉ (searchKernel G).fv := by simp
  have h₁ : Beta (app (searchKernel G) (searchKernel G))
      (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (var 4))
        (app (app (searchKernel G) (searchKernel G)) (app successorTerm (var 4))))) := by
    convert Beta.contract 3 (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (var 4))
      (app (app (var 3) (var 3)) (app successorTerm (var 4))))) (searchKernel G) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) hK]
    simp [subst_app, subst_var, subst_not_free _ _ _ (hf 3 (by decide)),
      subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ successorTerm_closed]
  have h₂ : Beta (app (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (var 4))
      (app (app (searchKernel G) (searchKernel G)) (app successorTerm (var 4))))) (numeral k))
      (app (app (app zeroTestTerm (app G (numeral k))) (numeral k))
        (app (app (searchKernel G) (searchKernel G)) (app successorTerm (numeral k)))) := by
    convert Beta.contract 4 (app (app (app zeroTestTerm (app G (var 4))) (var 4))
      (app (app (searchKernel G) (searchKernel G)) (app successorTerm (var 4)))) (numeral k) using 1
    simp [subst_app, subst_var, subst_not_free _ _ _ (hf 4 (by decide)),
      subst_not_free _ _ _ hK, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ successorTerm_closed]
  exact .tail (.single (.app_left _ h₁)) h₂

/-- The successful branch does not evaluate the recursive continuation. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    If $k<j$, reduce the test to the positive numeral supplied by the hypothesis. Zero testing selects the continuation, and successor reduces its argument to $\ChurchNumeral{k+1}$. Thus
    $$\LambdaInputSteps{p}{S_k}{S_{k+1}}\qquad(k<j).$$
    At $k=j$, the test reduces to $\ChurchNumeral{0}$, so the other branch returns $\ChurchNumeral{j}$. It discards the continuation without reducing it.
-/
theorem searchFrom_zero {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0}) (k : ℕ)
    (h : Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral 0)) :
    Relation.ReflTransGen (OracleStep p) (searchFrom G k) (numeral k) := by
  apply (beta_steps_oracle (searchFrom_unfold hG k)).trans
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm h) _) _).trans
  exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    If $k<j$, reduce the test to the positive numeral supplied by the hypothesis. Zero testing selects the continuation, and successor reduces its argument to $\ChurchNumeral{k+1}$. Thus
    $$\LambdaInputSteps{p}{S_k}{S_{k+1}}\qquad(k<j).$$
    At $k=j$, the test reduces to $\ChurchNumeral{0}$, so the other branch returns $\ChurchNumeral{j}$. It discards the continuation without reducing it.
-/
theorem searchFrom_next {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0}) (k r : ℕ)
    (h : Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral (r + 1))) :
    Relation.ReflTransGen (OracleStep p) (searchFrom G k) (searchFrom G (k + 1)) := by
  apply (beta_steps_oracle (searchFrom_unfold hG k)).trans
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm h) _) _).trans
  exact (beta_steps_oracle (branch_succ r _ _)).trans
    (oracle_steps_app_right _ (beta_steps_oracle (successorTerm_apply k)))

/-- Only tests in the finite successful prefix are assumed to terminate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Starting from the successful case and working backwards through the finitely many preceding candidates proves that every $S_k$ with $k\le j$ reduces to $\ChurchNumeral{j}$. In particular, this holds for $S_0$, including when $j=0$. All concatenated reductions are finite. The wrapper is closed because $H$ and the search term are closed and both remaining arguments are bound. Confluence excludes any other numeral output, giving the exact-output condition on $D$. Neither the term nor the proof requires a uniform bound on $j(p,n)$ or a test for membership in $D$.
-/
theorem searchFrom_hit {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0}) (j : ℕ)
    (hzero : Relation.ReflTransGen (OracleStep p) (app G (numeral j)) (numeral 0))
    (hpos : ∀ k < j, ∃ r, Relation.ReflTransGen (OracleStep p)
      (app G (numeral k)) (numeral (r + 1))) :
    ∀ k ≤ j, Relation.ReflTransGen (OracleStep p) (searchFrom G k) (numeral j) := by
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self => exact searchFrom_zero hG j hzero
  | of_succ k hk ih =>
    obtain ⟨r, hr⟩ := hpos k hk
    exact (searchFrom_next hG k r hr).trans ih

/-- The same test term is used for every name, output coordinate and candidate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Use the search term of §{sec:lambda-numerical-search} with tests that may query the input name. For a closed term $H$, define the closed wrapper
    $$\LambdaSearchProgram{H}:=\lambdaab{a}{\lambdaab{b}{\LambdaSearch\,(Hab)}}.$$
    Here $a$ supplies the input name and $b$ supplies the output coordinate. The test itself is the term $Hab$.
-/
def searchProgram (H : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app searchTerm (app (app H (var 1)) (var 2))))

theorem searchProgram_closed {H : AlphaTerm} (hH : H.Closed) : (searchProgram H).Closed := by
  unfold Closed searchProgram
  simp only [fv_lam, fv_app, fv_var]
  rw [searchTerm_closed, hH]
  decide

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Fix $p,n$ and abbreviate $G:=H\,o\,\ChurchNumeral{n}$ and $j:=j(p,n)$. The only possible free variable of $G$ is $o$. Choose the kernel binders different from $o$ and set
    $$S_k:=\bigl(\LambdaSearchKernel{G}\,\LambdaSearchKernel{G}\bigr)\ChurchNumeral{k}.$$
    The two outer beta steps of the wrapper, followed by the beta step of the search term, produce $S_0$. Two beta steps unfold the self-application at any candidate:
    $$S_k\to_\beta^*
    \LambdaZeroTest\,(G\ChurchNumeral{k})\,\ChurchNumeral{k}\,
    \bigl((\LambdaSearchKernel{G}\,\LambdaSearchKernel{G})(\LambdaSucc\,\ChurchNumeral{k})\bigr).$$
    Freshness of the binders preserves the test term and the duplicated kernel in these substitutions.
-/
theorem searchProgram_start {H : AlphaTerm} (hH : H.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (searchProgram H) (var 0)) (numeral n))
      (searchFrom (app (app H (var 0)) (numeral n)) 0) := by
  have hf (x : ℕ) : x ∉ H.fv := by rw [hH]; simp
  have h₁ : Beta (app (searchProgram H) (var 0))
      (lam 2 (app searchTerm (app (app H (var 0)) (var 2)))) := by
    convert Beta.contract 1 (lam 2 (app searchTerm (app (app H (var 1)) (var 2)))) (var 0)
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app, subst_var, subst_closed _ _ _ searchTerm_closed, subst_not_free _ _ _ (hf 1)]
  have h₂ : Beta (app (lam 2 (app searchTerm (app (app H (var 0)) (var 2)))) (numeral n))
      (app searchTerm (app (app H (var 0)) (numeral n))) := by
    convert Beta.contract 2 (app searchTerm (app (app H (var 0)) (var 2))) (numeral n)
      using 1
    simp [subst_app, subst_var, subst_closed _ _ _ searchTerm_closed, subst_not_free _ _ _ (hf 2)]
  have hG : (app (app H (var 0)) (numeral n)).fv ⊆ {0} := by
    rw [fv_app, fv_app, hH, numeral_closed, fv_var]
    simp
  exact .tail (.tail (.single (.app_left _ h₁)) h₂) (searchTerm_start hG)

/-- The successful prefix may depend on the input name and coordinate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Sequential search by a closed lambda term
-/
theorem searchProgram_hit {p : ℕ → ℕ} {H : AlphaTerm} (hH : H.Closed) (n j : ℕ)
    (hzero : Relation.ReflTransGen (OracleStep p)
      (app (app (app H (var 0)) (numeral n)) (numeral j)) (numeral 0))
    (hpos : ∀ k < j, ∃ r, Relation.ReflTransGen (OracleStep p)
      (app (app (app H (var 0)) (numeral n)) (numeral k)) (numeral (r + 1))) :
    OracleRuns p (searchProgram H) n j := by
  have hG : (app (app H (var 0)) (numeral n)).fv ⊆ {0} := by
    rw [fv_app, fv_app, hH, numeral_closed, fv_var]
    simp
  exact (beta_steps_oracle (searchProgram_start hH n)).trans
    (searchFrom_hit hG j hzero hpos 0 (Nat.zero_le j))

/-- This statement imposes no conditions on tests after the returned candidate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Starting from the successful case and working backwards through the finitely many preceding candidates proves that every $S_k$ with $k\le j$ reduces to $\ChurchNumeral{j}$. In particular, this holds for $S_0$, including when $j=0$. All concatenated reductions are finite. The wrapper is closed because $H$ and the search term are closed and both remaining arguments are bound. Confluence excludes any other numeral output, giving the exact-output condition on $D$. Neither the term nor the proof requires a uniform bound on $j(p,n)$ or a test for membership in $D$.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Sequential search by a closed lambda term
-/
theorem searchProgram_typeTwoComputes {D : Set (ℕ → ℕ)} {H : AlphaTerm}
    (hH : H.Closed) (μ : D → ℕ → ℕ)
    (hzero : ∀ (p : D) n, Relation.ReflTransGen (OracleStep p.val)
      (app (app (app H (var 0)) (numeral n)) (numeral (μ p n))) (numeral 0))
    (hpos : ∀ (p : D) n k, k < μ p n → ∃ r, Relation.ReflTransGen (OracleStep p.val)
      (app (app (app H (var 0)) (numeral n)) (numeral k)) (numeral (r + 1))) :
    TypeTwoComputes (searchProgram H) μ := by
  rw [typeTwoComputes_iff_runs]
  exact ⟨searchProgram_closed hH, fun p n => searchProgram_hit hH n (μ p n) (hzero p n) (hpos p n)⟩

/-- Total numerical tests with a zero witness give least-witness search. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    The nonempty set of successful candidates has a least element. At every smaller candidate, the total numerical test returns a nonzero natural number, hence a successor numeral. Apply the theorem to this least element.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Least-witness search
-/
theorem searchProgram_least {D : Set (ℕ → ℕ)} {H : AlphaTerm} (hH : H.Closed)
    (f : D → ℕ → ℕ → ℕ)
    (htest : ∀ (p : D) n k, Relation.ReflTransGen (OracleStep p.val)
      (app (app (app H (var 0)) (numeral n)) (numeral k)) (numeral (f p n k)))
    (hex : ∀ (p : D) n, ∃ k, f p n k = 0) :
    TypeTwoComputes (searchProgram H) (fun p n => Nat.find (hex p n)) := by
  apply searchProgram_typeTwoComputes hH
  · intro p n
    simpa only [Nat.find_spec (hex p n)] using htest p n (Nat.find (hex p n))
  · intro p n k hk
    cases he : f p n k with
    | zero => exact False.elim (Nat.find_min (hex p n) hk he)
    | succ r => exact ⟨r, by simpa only [he, Nat.succ_eq_add_one] using htest p n k⟩

/-- Find the first zero of a name, uniformly on the domain where a zero exists. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Three beta steps and one query reduce $H\,o\,\ChurchNumeral{n}\,\ChurchNumeral{k}$ to $\ChurchNumeral{p(k)}$. Thus the test is total, independently of $n$, and the definition of $D$ supplies a zero witness. Apply the corollary.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: example
  title: Finding the first zero of an input name
-/
theorem inputZeroSearch_typeTwoComputes {D : Set (ℕ → ℕ)}
    (hex : ∀ p : D, ∃ k, p.val k = 0) :
    TypeTwoComputes (searchProgram inputIterationStep) (fun p _ => Nat.find (hex p)) := by
  exact searchProgram_least inputIterationStep_closed (fun p _ k => p.val k)
    (fun p n k => inputIterationStep_apply p.val n k) (fun p _ => hex p)

end PolishSpaceBook.NamedLambda.AlphaTerm
