module

public import PolishSpaceBook.LambdaNumericalFunctions
public import PolishSpaceBook.LambdaSearchResult

@[expose] public section

/-! # Parameterized numerical search in the lambda calculus

A total test on paired input is searched sequentially. The result is the least
stage with a nonzero answer; no such stage means no numeral output.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def curryNumerical (F : AlphaTerm) : AlphaTerm :=
  lam 40 (lam 41 (app F (app (app numericalPairTerm (var 40)) (var 41))))

theorem curryNumerical_closed {F : AlphaTerm} (hF : F.Closed) : (curryNumerical F).Closed := by
  unfold curryNumerical Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hF,numericalPairTerm_closed]
  decide

theorem curryNumerical_apply {F : AlphaTerm} (hF : F.Closed) (n k : ℕ) :
    Relation.ReflTransGen Beta (app (app (curryNumerical F) (numeral n)) (numeral k))
      (app F (numeral (Nat.pair n k))) := by
  have he : (lam 41 (app F (app (app numericalPairTerm (var 40)) (var 41)))).subst 40 (numeral n) =
      lam 41 (app F (app (app numericalPairTerm (numeral n)) (var 41))) := by
    rw [subst_lam_fresh _ _ 41 40 (by decide) (by rw [numeral_closed]; simp)]
    simp only [subst_app,subst_var,subst_closed _ _ _ hF,
      subst_closed _ _ _ numericalPairTerm_closed]
    simp
  have h₁ : Beta (app (curryNumerical F) (numeral n))
      (lam 41 (app F (app (app numericalPairTerm (numeral n)) (var 41)))) := by
    rw [← he]; exact Beta.contract 40 _ _
  have h₂ : Beta (app (lam 41 (app F (app (app numericalPairTerm (numeral n)) (var 41)))) (numeral k))
      (app F (app (app numericalPairTerm (numeral n)) (numeral k))) := by
    simpa only [subst_app,subst_var,ite_true,subst_closed _ _ _ hF,
      subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed n)] using
      Beta.contract 41 (app F (app (app numericalPairTerm (numeral n)) (var 41))) (numeral k)
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    (beta_steps_app_right F (numericalPairTerm_apply n k))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P$ be a closed program deciding $(s,t)\in T_i$ at parameter $\varepsilon$ on input
    $\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Throughout this subsection, expand all abbreviations before abstraction and choose distinct fresh binders.
    For a node code $z$, put
    $$\begin{aligned}
    d(z)&:=\LambdaListField{2}(\LambdaNumericProjection{2}z),\qquad
    h(z):=\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,\ChurchNumeral{0}),\\
    Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The field program also returns zero at the empty-list code, so it computes the tail code for every list.
    The term $Z$ reverses a decision bit.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here we give the programs used for effective separation. A pair tree is a downward-closed set of equal-length
    pairs of finite words. Its section at $x$ consists of the words $u$ with $(\restrict{x}{|u|},u)$ in the tree,
    with the empty word added. Suppose closed programs $P_T,P_S$ decide two families of pair trees at the same
    parameter, on input $\NatPair{i}{\NatPair{a}{b}}$, where $a,b$ are word codes. In this subsection,
    expand all abbreviations before abstraction and choose fresh binders. The symbol $Z$ denotes the numerical
    zero test returning one on zero and zero otherwise.
-/
def reverseZeroTerm : AlphaTerm :=
  lam 40 (app (app (app zeroTestTerm (var 40)) (numeral 1)) (numeral 0))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P$ be a closed program deciding $(s,t)\in T_i$ at parameter $\varepsilon$ on input
    $\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Throughout this subsection, expand all abbreviations before abstraction and choose distinct fresh binders.
    For a node code $z$, put
    $$\begin{aligned}
    d(z)&:=\LambdaListField{2}(\LambdaNumericProjection{2}z),\qquad
    h(z):=\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,\ChurchNumeral{0}),\\
    Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The field program also returns zero at the empty-list code, so it computes the tail code for every list.
    The term $Z$ reverses a decision bit.
-/
theorem reverseZero_computes : NumericalComputes reverseZeroTerm (fun n => if n = 0 then 1 else 0) := by
  refine ⟨?_,fun n => ?_⟩
  · unfold reverseZeroTerm Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [zeroTestTerm_closed,numeral_closed,numeral_closed]
    decide
  · have hs : Beta (app reverseZeroTerm (numeral n))
        (app (app (app zeroTestTerm (numeral n)) (numeral 1)) (numeral 0)) := by
      simpa only [reverseZeroTerm,subst_app,subst_var,ite_true,
        subst_closed _ _ _ zeroTestTerm_closed,subst_closed _ _ _ (numeral_closed _)] using
        Beta.contract 40 (app (app (app zeroTestTerm (var 40)) (numeral 1)) (numeral 0)) (numeral n)
    apply (Relation.ReflTransGen.single hs).trans
    cases n with
    | zero => exact branch_zero _ _ (by rw [numeral_closed]; simp)
    | succ n => exact branch_succ n _ _

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first make ordinary numerical search with a parameter explicit. Let a closed term $T$ compute a total numerical
    function $t$ on paired inputs. Put
    $$\begin{aligned}
    I&:=\lambdaab{x}{x},\\
    G_z&:=\lambdaab{k}{\LambdaZeroTest\,(T\,(\LambdaNumericPair\,z\,k))\,
      \ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    S_T&:=\lambdaab{z}{\LambdaResultSearch\,G_z\,I}.
    \end{aligned}$$
    All these computations use ordinary beta reduction. There is no input-name variable.
-/
def numericalSearch (F : AlphaTerm) : AlphaTerm :=
  lam 42 (app (app resultSearchTerm
    (app (curryNumerical (numericalCompose reverseZeroTerm F)) (var 42))) numericalIdentity)

theorem numericalSearch_closed {F : AlphaTerm} (hF : F.Closed) : (numericalSearch F).Closed := by
  have hc : (numericalCompose reverseZeroTerm F).Closed := by
    unfold numericalCompose Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [reverseZero_computes.1,hF]
    decide
  unfold numericalSearch Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [resultSearchTerm_closed,curryNumerical_closed hc,numericalIdentity_computes.1]
  decide

theorem numericalSearch_start {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) (n : ℕ) :
    Relation.ReflTransGen Beta (app (numericalSearch F) (numeral n))
      (app (app resultSearchTerm
        (app (curryNumerical (numericalCompose reverseZeroTerm F)) (numeral n))) numericalIdentity) := by
  apply Relation.ReflTransGen.single
  simpa only [numericalSearch,subst_app,subst_var,ite_true,
    subst_closed _ _ _ resultSearchTerm_closed,subst_closed _ _ _ numericalIdentity_computes.1,
    subst_closed _ _ _ (curryNumerical_closed (reverseZero_computes.comp hf).1)] using
    Beta.contract 42 (app (app resultSearchTerm
      (app (curryNumerical (numericalCompose reverseZeroTerm F)) (var 42))) numericalIdentity) (numeral n)

theorem numericalSearch_hit {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f)
    (n j : ℕ) (hj : f (Nat.pair n j) ≠ 0) (hb : ∀ k < j, f (Nat.pair n k) = 0) :
    Relation.ReflTransGen Beta (app (numericalSearch F) (numeral n)) (numeral j) := by
  have ht := reverseZero_computes.comp hf
  have hs (k : ℕ) := (curryNumerical_apply ht.1 n k).trans (ht.2 (Nat.pair n k))
  apply (numericalSearch_start hf n).trans
  apply (resultSearchTerm_hit (closed_app (curryNumerical_closed ht.1) (numeral_closed n))
    numericalIdentity_computes.1 j (by simpa [hj] using hs j)
    (fun k hk => ⟨0,by simpa [hb k hk] using hs k⟩)).trans
  exact numericalIdentity_computes.2 j

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Parameterized numerical search
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Contract the outer abstraction, compute the numerical pair and run $T$. Every stage terminates. The zero test returns
    zero exactly when $T$ returns a positive numeral. The result-search lemma therefore reaches the least successful stage
    and applies $I$ to its numeral. If no stage succeeds, the reversed test always returns one, so the same lemma excludes
    every numeral output. Confluence transports this conclusion across the outer contraction. To implement the displayed
    formula by our composition helpers, curry the paired-input term, compose with zero testing, and pass the resulting unary
    test to result search; the additional beta contractions give exactly the same test. All free variables are bound, so the
    assembled program is closed.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first make ordinary numerical search with a parameter explicit. Let a closed term $T$ compute a total numerical
    function $t$ on paired inputs. Put
    $$\begin{aligned}
    I&:=\lambdaab{x}{x},\\
    G_z&:=\lambdaab{k}{\LambdaZeroTest\,(T\,(\LambdaNumericPair\,z\,k))\,
      \ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    S_T&:=\lambdaab{z}{\LambdaResultSearch\,G_z\,I}.
    \end{aligned}$$
    All these computations use ordinary beta reduction. There is no input-name variable.
-/
theorem numericalSearch_domain {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) (n : ℕ) :
    (∃ m, Relation.ReflTransGen Beta (app (numericalSearch F) (numeral n)) (numeral m)) ↔
      ∃ k, f (Nat.pair n k) ≠ 0 := by
  classical
  constructor
  · rintro ⟨m,hm⟩
    by_contra hn
    have hn : ∀ k, f (Nat.pair n k) = 0 := by simpa using hn
    have ht := reverseZero_computes.comp hf
    have hs (k : ℕ) := (curryNumerical_apply ht.1 n k).trans (ht.2 (Nat.pair n k))
    exact resultSearchTerm_no_output (closed_app (curryNumerical_closed ht.1) (numeral_closed n))
      numericalIdentity_computes.1 (fun k => ⟨0,by simpa [hn k] using hs k⟩) m
      (numeral_after_reduction (numericalSearch_start hf n) hm)
  · intro h
    exact ⟨Nat.find h,numericalSearch_hit hf n (Nat.find h) (Nat.find_spec h)
      (fun _ hk => not_ne_iff.mp (Nat.find_min h hk))⟩

noncomputable def firstNumericalHit (f : ℕ → ℕ) (h : ∀ n, ∃ k, f (Nat.pair n k) ≠ 0) (n : ℕ) :=
  Nat.find (h n)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Parameterized numerical search
-/
theorem numericalSearch_computes {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f)
    (h : ∀ n, ∃ k, f (Nat.pair n k) ≠ 0) :
    NumericalComputes (numericalSearch F) (firstNumericalHit f h) :=
  ⟨numericalSearch_closed hf.1,fun n => numericalSearch_hit hf n _ (Nat.find_spec (h n))
    (fun _ hk => not_ne_iff.mp (Nat.find_min (h n) hk))⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
