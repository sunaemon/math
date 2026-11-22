module

public import PolishSpaceBook.LambdaOracleReduction

@[expose] public section

/-! # Identity and constant lambda realizers -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm

/-- Confluence turns existence of the intended output into an exact graph. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$ for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example, $\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term $\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps return that numeral. Both terms are closed.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$
    for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example,
    $\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term
    $\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps
    return that numeral. Both terms are closed.
-/
theorem typeTwoComputes_iff_runs {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)} {P : AlphaTerm} :
    TypeTwoComputes P F ↔ P.Closed ∧ ∀ p n, OracleRuns p.val P n (F p n) := by
  constructor
  · intro h
    exact ⟨h.1, fun p n => (h.2 p n (F p n)).mpr rfl⟩
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun p n m => ⟨?_, ?_⟩⟩
    · intro hm
      exact (h p n).output_unique hm
    · intro he
      rw [← he]
      exact h p n

namespace NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$
    for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example,
    $\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term
    $\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps
    return that numeral. Both terms are closed.
-/
def identityProgram : AlphaTerm := lam 1 (var 1)

@[simp] theorem identityProgram_closed : identityProgram.Closed := by
  unfold Closed identityProgram
  rw [fv_lam]
  change ({1} : Finset ℕ).erase 1 = ∅
  simp

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$
    for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example,
    $\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term
    $\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps
    return that numeral. Both terms are closed.
-/
theorem identityProgram_runs (p : ℕ → ℕ) (n : ℕ) :
    OracleRuns p identityProgram n (p n) := by
  have h : Beta (app identityProgram (var 0)) (var 0) := by
    simpa [identityProgram, subst_var] using (Beta.contract 1 (var 1) (var 0))
  exact .tail (.single (.beta (.app_left (numeral n) h))) (.query n)

/-- Constant numerical output, ignoring the name and the coordinate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$
    for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example,
    $\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term
    $\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps
    return that numeral. Both terms are closed.
-/
def constantProgram (m : ℕ) : AlphaTerm := lam 1 (lam 2 (numeral m))

@[simp] theorem constantProgram_closed (m : ℕ) : (constantProgram m).Closed := by
  unfold Closed constantProgram
  rw [fv_lam, fv_lam, numeral_closed]
  simp

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$
    for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example,
    $\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term
    $\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps
    return that numeral. Both terms are closed.
-/
theorem constantProgram_runs (m : ℕ) (p : ℕ → ℕ) (n : ℕ) :
    OracleRuns p (constantProgram m) n m := by
  have h : Beta (app (constantProgram m) (var 0)) (lam 2 (numeral m)) := by
    have hf : 1 ∉ (lam 2 (numeral m)).fv := by rw [fv_lam, numeral_closed]; simp
    simpa only [constantProgram, subst_not_free _ _ _ hf]
      using (Beta.contract 1 (lam 2 (numeral m)) (var 0))
  have h' : Beta (app (lam 2 (numeral m)) (numeral n)) (numeral m) := by
    have hf : 2 ∉ (numeral m).fv := by rw [numeral_closed]; simp
    simpa only [subst_not_free _ _ _ hf] using (Beta.contract 2 (numeral m) (numeral n))
  exact .tail (.single (.beta (.app_left (numeral n) h))) (.beta h')

/-- Feed the name computed by Q to P, using ordinary lambda application. -/
def compositionProgram (P Q : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app (app P (app Q (var 1))) (var 2)))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
theorem compositionProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (compositionProgram P Q).Closed := by
  change P.fv = ∅ at hP
  change Q.fv = ∅ at hQ
  unfold Closed compositionProgram
  simp only [fv_lam, fv_app, hP, hQ, Finset.empty_union]
  change ((({1} : Finset ℕ) ∪ {2}).erase 2).erase 1 = ∅
  decide

theorem compositionProgram_start {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    (p : ℕ → ℕ) (n : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (compositionProgram P Q) (var 0)) (numeral n))
      (app (app P (app Q (var 0))) (numeral n)) := by
  have hPf (x : ℕ) : x ∉ P.fv := by rw [hP]; simp
  have hQf (x : ℕ) : x ∉ Q.fv := by rw [hQ]; simp
  have hf : 2 ∉ (var 0).fv := by change 2 ∉ ({0} : Finset ℕ); decide
  have h₁ : Beta (app (compositionProgram P Q) (var 0))
      (lam 2 (app (app P (app Q (var 0))) (var 2))) := by
    convert Beta.contract 1 (lam 2 (app (app P (app Q (var 1))) (var 2))) (var 0) using 1 <;>
      simp [compositionProgram, subst_lam_fresh _ _ 2 1 (by decide) hf,
      subst_app, subst_var, subst_not_free P _ _ (hPf 1), subst_not_free Q _ _ (hQf 1)]
  have h₂ : Beta (app (lam 2 (app (app P (app Q (var 0))) (var 2))) (numeral n))
      (app (app P (app Q (var 0))) (numeral n)) := by
    convert Beta.contract 2 (app (app P (app Q (var 0))) (var 2)) (numeral n) using 1
    simp [subst_app, subst_var, subst_not_free P _ _ (hPf 2), subst_not_free Q _ _ (hQf 2)]
  exact .tail (.single (.beta (.app_left _ h₁))) (.beta h₂)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Two beta steps reduce $C_{P,Q}\,o\,\ChurchNumeral{n}$ to $P\,(Q\,o)\,\ChurchNumeral{n}$. Since $P$ is closed, this is exactly the result of substituting $R$ for $o$ in $P\,o\,\ChurchNumeral{n}$. The preceding argument supplies the required output, and confluence excludes other numeral outputs. Closedness of $P,Q$ also gives closedness of $C_{P,Q}$. The identity computation was verified above.
-/
theorem compositionProgram_runs {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    {p q : ℕ → ℕ} {n m : ℕ} (h : OracleRuns q P n m)
    (hq : ∀ k, OracleRuns p Q k (q k)) :
    OracleRuns p (compositionProgram P Q) n m := by
  apply (compositionProgram_start hP hQ p n).trans
  have hs := oracle_steps_subst_input (R := app Q (var 0)) h hq
  have hPf : 0 ∉ P.fv := by rw [hP]; simp
  have hnf (k : ℕ) : 0 ∉ (numeral k).fv := by rw [numeral_closed]; simp
  simpa [subst_app, subst_var, subst_not_free P _ _ hPf,
    subst_not_free (numeral n) _ _ (hnf n), subst_not_free (numeral m) _ _ (hnf m)] using hs
end NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termuseas{uniform oracle substitution lemma}{Lambda substitution and composition}]
-/
theorem identityProgram_computes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes identityProgram (fun p : D => p.val) :=
  typeTwoComputes_iff_runs.mpr ⟨identityProgram_closed, fun p n => identityProgram_runs p.val n⟩

theorem constantProgram_computes (D : Set (ℕ → ℕ)) (m : ℕ) :
    TypeTwoComputes (constantProgram m) (fun _ : D => fun _ => m) :=
  typeTwoComputes_iff_runs.mpr ⟨constantProgram_closed m, fun p n => constantProgram_runs m p.val n⟩
/-- Composition is realized by substituting one lambda name producer into another. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: lemma
  title: Lambda substitution and composition
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termuseas{uniform oracle substitution lemma}{Lambda substitution and composition}]
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To compute an output coordinate, run the outer program and answer each request for an intermediate digit by running the
    inner program at that digit. Every such inner computation terminates on a valid input. The outer computation uses
    finitely many requests, so replacing each request by its inner computation still gives a finite computation with the
    required output. Substitution implements exactly this procedure in the displayed term. Output uniqueness excludes any
    other numeral. The domains require only that every intermediate name be valid for the outer map. The substitution
    argument in full is proved in §{sec:lambda-input-composition}.
-/
theorem TypeTwoComputes.comp {D E : Set (ℕ → ℕ)} {F : D → E} {G : E → (ℕ → ℕ)}
    {P Q : AlphaTerm} (hP : TypeTwoComputes P G)
    (hQ : TypeTwoComputes Q (fun p => (F p).val)) :
    TypeTwoComputes (compositionProgram P Q) (fun p => G (F p)) := by
  apply typeTwoComputes_iff_runs.mpr
  refine ⟨compositionProgram_closed hP.1 hQ.1, fun p n => ?_⟩
  exact compositionProgram_runs hP.1 hQ.1 ((hP.2 (F p) n _).mpr rfl)
    (fun k => (hQ.2 p k _).mpr rfl)
end PolishSpaceBook
