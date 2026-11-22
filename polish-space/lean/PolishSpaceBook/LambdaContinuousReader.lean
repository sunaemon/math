module

public import PolishSpaceBook.LambdaInputPrefixes
public import PolishSpaceBook.LambdaProducts
public import PolishSpaceBook.LambdaOracleSearchResult

@[expose] public section

/-! # A fixed lambda reader for cylinder certificates

At stage k = pair N v, read the first N digits of the right input name and
ask the left name about pair n (pair (list-code prefix) v). A nonzero answer
certifies v. Every trial is total, even on arbitrary joined input names.
-/
namespace PolishSpaceBook
open NamedLambda
namespace NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-- Access either component of the joined input through an actual lambda term. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Join two names pointwise by $w(j):=\NatPair{r(j)}{p(j)}$. The left component $r$ will describe a continuous map, and the right component $p$ will be its input. To access either component, put $I:=\lambdaab{x}{x}$ and
    $$\LambdaNameAccessor{i}{A}:=
     (\lambdaab{a}{\lambdaab{j}{\LambdaNumericProjection{i}\,(Iaj)}})A
     \qquad(i=1,2).$$
    The outer binders are fresh for $A$. On input $w$, the term $\LambdaNameAccessor{1}{o}\,\ChurchNumeral{j}$ returns $\ChurchNumeral{r(j)}$, and the second accessor returns $\ChurchNumeral{p(j)}$. This follows by the two outer beta steps, the identity reduction, one query and numerical projection.
-/
def nameAccessor (first : Bool) (O : AlphaTerm) : AlphaTerm :=
  app (projectOutputProgram first identityProgram) O

theorem nameAccessor_fv (first : Bool) (O : AlphaTerm) :
    (nameAccessor first O).fv = O.fv := by
  rw [nameAccessor, projectOutputProgram, fv_app, mapOutputProgram_closed (numericalProjectionTerm_closed first)
    identityProgram_closed, Finset.empty_union]

theorem nameAccessor_subst (first : Bool) (O W : AlphaTerm) (x : ℕ) :
    (nameAccessor first O).subst x W = nameAccessor first (O.subst x W) := by
  simp only [nameAccessor, projectOutputProgram, subst_app, subst_closed _ _ _
    (mapOutputProgram_closed (numericalProjectionTerm_closed first) identityProgram_closed)]

theorem nameAccessor_apply (first : Bool) (p : ℕ → ℕ) (k : ℕ) :
    Relation.ReflTransGen (OracleStep p) (app (nameAccessor first (var 0)) (numeral k))
      (numeral (if first then (p k).unpair.1 else (p k).unpair.2)) :=
  mapOutputProgram_runs (numericalProjectionTerm_closed first) identityProgram_closed
    (identityProgram_runs p k) (numericalProjectionTerm_apply first (p k))

/-- A concrete triple code, using the same list and pairing codes as the reader. -/
def continuousQuery (w : ℕ → ℕ) (n k : ℕ) : ℕ :=
  typeTwoLeftName w (Nat.pair n (Nat.pair
    (NatListCode.encode (seqPrefix (typeTwoRightName w) k.unpair.1)) k.unpair.2))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    At stage $k=\NatPair{N}{v}$, read the prefix of length $N$ and ask whether it certifies output $v$ at coordinate $n$. Encode the triple consisting of a coordinate, a finite sequence and a value by $\NatPair{n}{\NatPair{\LambdaListCode{s}}{v}}$. The corresponding open terms are
    $$\begin{aligned}
    \LambdaCylinderPrefix{A}{K}&:=\LambdaInputPrefix\,
     (\LambdaNameAccessor{2}{A})\,(\LambdaNumericProjection{1}\,K),\\
    \LambdaCylinderQuery{A}{B}{K}&:=\LambdaNameAccessor{1}{A}\,\bigl(
     \LambdaNumericPair\,B\,(
     \LambdaNumericPair\,\LambdaCylinderPrefix{A}{K}\,
     (\LambdaNumericProjection{2}\,K))\bigr).
    \end{aligned}$$
    Here $B$ in the term expression is the argument for the output coordinate; the stage projections determine the prefix length and candidate value. The query returns the certificate name's actual digit, which may be any natural number.
-/
def continuousQueryBody (O N K : AlphaTerm) : AlphaTerm :=
  app (nameAccessor true O) (app (app numericalPairTerm N)
    (app (app numericalPairTerm
      (app (app prefixProgram (nameAccessor false O)) (app (numericalProjectionTerm true) K)))
      (app (numericalProjectionTerm false) K)))

theorem continuousQueryBody_fv (O N K : AlphaTerm) :
    (continuousQueryBody O N K).fv = O.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [continuousQueryBody, fv_app, nameAccessor_fv,
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),
    (show prefixProgram.fv = ∅ from prefixProgram_closed),
    (show (numericalProjectionTerm true).fv = ∅ from numericalProjectionTerm_closed true),
    (show (numericalProjectionTerm false).fv = ∅ from numericalProjectionTerm_closed false),
    Finset.mem_union, Finset.notMem_empty]
  tauto

theorem continuousQueryBody_subst (O N K W : AlphaTerm) (x : ℕ) :
    (continuousQueryBody O N K).subst x W =
      continuousQueryBody (O.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [continuousQueryBody, subst_app, nameAccessor_subst,
    subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ prefixProgram_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false)]

theorem continuousQueryBody_apply (w : ℕ → ℕ) (n k : ℕ) :
    Relation.ReflTransGen (OracleStep w)
      (continuousQueryBody (var 0) (numeral n) (numeral k)) (numeral (continuousQuery w n k)) := by
  have hp := prefixProgram_apply_upto (p := w) (q := typeTwoRightName w)
    (O := nameAccessor false (var 0)) (by rw [nameAccessor_fv, fv_var]) k.unpair.1
    (fun i _ => nameAccessor_apply false w i)
  have hN := beta_steps_oracle (p := w) (numericalProjectionTerm_apply true k)
  have hv := beta_steps_oracle (p := w) (numericalProjectionTerm_apply false k)
  have hs := (oracle_steps_app_right (app prefixProgram (nameAccessor false (var 0))) hN).trans hp
  have hpair := (oracle_steps_app (oracle_steps_app_right numericalPairTerm hs) hv).trans
    (beta_steps_oracle (numericalPairTerm_apply _ _))
  have hcode := (oracle_steps_app_right (app numericalPairTerm (numeral n)) hpair).trans
    (beta_steps_oracle (numericalPairTerm_apply _ _))
  exact (oracle_steps_app_right (nameAccessor true (var 0)) hcode).trans
    (nameAccessor_apply true w _)

/-- Invert the certificate bit to use the zero-success search convention. -/
def continuousTestBody (O N K : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (continuousQueryBody O N K)) (numeral 1)) (numeral 0)

theorem continuousTestBody_fv (O N K : AlphaTerm) :
    (continuousTestBody O N K).fv = O.fv ∪ N.fv ∪ K.fv := by
  simp only [continuousTestBody, fv_app, continuousQueryBody_fv,
    (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed),
    (show (numeral 1).fv = ∅ from numeral_closed 1),
    (show (numeral 0).fv = ∅ from numeral_closed 0), Finset.empty_union, Finset.union_empty]

theorem continuousTestBody_subst (O N K W : AlphaTerm) (x : ℕ) :
    (continuousTestBody O N K).subst x W =
      continuousTestBody (O.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [continuousTestBody, subst_app, continuousQueryBody_subst,
    subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ (numeral_closed 1), subst_closed _ _ _ (numeral_closed 0)]

def continuousTest (O N : AlphaTerm) : AlphaTerm :=
  lam 43 (continuousTestBody O N (var 43))

theorem continuousTest_fv (O N : AlphaTerm) :
    (continuousTest O N).fv = (O.fv ∪ N.fv).erase 43 := by
  ext x
  simp only [continuousTest, fv_lam, continuousTestBody_fv, fv_var,
    Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
  tauto

theorem continuousTest_subst (O N W : AlphaTerm) (x : ℕ) (hx : 43 ≠ x) (hW : 43 ∉ W.fv) :
    (continuousTest O N).subst x W = continuousTest (O.subst x W) (N.subst x W) := by
  rw [continuousTest, subst_lam_fresh _ _ _ _ hx hW, continuousTestBody_subst]
  simp only [subst_var, ite_eq_right hx, continuousTest]

theorem continuousTest_input (n : ℕ) : (continuousTest (var 0) (numeral n)).fv ⊆ {0} := by
  rw [continuousTest_fv, fv_var, numeral_closed, Finset.union_empty]
  exact Finset.erase_subset _ _

theorem continuousTest_apply (w : ℕ → ℕ) (n k : ℕ) :
    Relation.ReflTransGen (OracleStep w)
      (app (continuousTest (var 0) (numeral n)) (numeral k))
      (numeral (if continuousQuery w n k = 0 then 1 else 0)) := by
  have he : (continuousTestBody (var 0) (numeral n) (var 43)).subst 43 (numeral k) =
      continuousTestBody (var 0) (numeral n) (numeral k) := by
    rw [continuousTestBody_subst, subst_closed _ _ _ (numeral_closed n)]
    simp [subst_var]
  have hb : Beta (app (continuousTest (var 0) (numeral n)) (numeral k))
      (continuousTestBody (var 0) (numeral n) (numeral k)) := by
    unfold continuousTest
    rw [← he]
    exact Beta.contract _ _ _
  apply (Relation.ReflTransGen.single (.beta hb)).trans
  apply (oracle_steps_app_left (oracle_steps_app_left
    (oracle_steps_app_right zeroTestTerm (continuousQueryBody_apply w n k)) (numeral 1)) (numeral 0)).trans
  cases h : continuousQuery w n k with
  | zero =>
    simp only [ite_true]
    exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | succ r =>
    simp only [Nat.succ_ne_zero, ite_false]
    exact beta_steps_oracle (branch_succ r _ _)

def continuousReaderBody (O N : AlphaTerm) : AlphaTerm :=
  app (app resultSearchTerm (continuousTest O N)) (numericalProjectionTerm false)

theorem continuousReaderBody_fv (O N : AlphaTerm) :
    (continuousReaderBody O N).fv = (O.fv ∪ N.fv).erase 43 := by
  simp only [continuousReaderBody, fv_app, continuousTest_fv,
    (show resultSearchTerm.fv = ∅ from resultSearchTerm_closed),
    (show (numericalProjectionTerm false).fv = ∅ from numericalProjectionTerm_closed false),
    Finset.empty_union, Finset.union_empty]

theorem continuousReaderBody_subst (O N W : AlphaTerm) (x : ℕ) (hx : 43 ≠ x) (hW : 43 ∉ W.fv) :
    (continuousReaderBody O N).subst x W = continuousReaderBody (O.subst x W) (N.subst x W) := by
  simp only [continuousReaderBody, subst_app, continuousTest_subst _ _ _ _ hx hW,
    subst_closed _ _ _ resultSearchTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed false)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Reverse the zero/nonzero test and use the second stage projection as the result function:
    $$\begin{aligned}
    \LambdaCylinderTest{A}{B}&:=\lambdaab{k}{\LambdaZeroTest\,
     \LambdaCylinderQuery{A}{B}{k}\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    \LambdaContinuousReader&:=\lambdaab{a}{\lambdaab{n}{
     \LambdaResultSearch\,\LambdaCylinderTest{a}{n}\,\LambdaNumericProjection{2}}}.
    \end{aligned}$$
    Expand all abbreviations before binding their parameters, choosing the internal binders fresh. This defines one closed finite lambda term, with no dependence on the domain or the map to be represented.
-/
def continuousReaderProgram : AlphaTerm :=
  lam 40 (lam 41 (continuousReaderBody (var 40) (var 41)))

@[simp] theorem continuousReaderProgram_closed : continuousReaderProgram.Closed := by
  unfold continuousReaderProgram Closed
  simp only [fv_lam, continuousReaderBody_fv, fv_var]
  decide

theorem continuousReaderProgram_start (n : ℕ) :
    Relation.ReflTransGen Beta (app (app continuousReaderProgram (var 0)) (numeral n))
      (continuousReaderBody (var 0) (numeral n)) := by
  have h₁ : Beta (app continuousReaderProgram (var 0))
      (lam 41 (continuousReaderBody (var 0) (var 41))) := by
    have he : (lam 41 (continuousReaderBody (var 40) (var 41))).subst 40 (var 0) =
        lam 41 (continuousReaderBody (var 0) (var 41)) := by
      rw [subst_lam_fresh _ _ 41 40 (by decide) (by simp [fv_var]),
        continuousReaderBody_subst _ _ _ _ (by decide) (by simp [fv_var])]
      simp [subst_var]
    unfold continuousReaderProgram
    rw [← he]
    exact Beta.contract _ _ _
  have h₂ : Beta (app (lam 41 (continuousReaderBody (var 0) (var 41))) (numeral n))
      (continuousReaderBody (var 0) (numeral n)) := by
    have he : (continuousReaderBody (var 0) (var 41)).subst 41 (numeral n) =
        continuousReaderBody (var 0) (numeral n) := by
      rw [continuousReaderBody_subst _ _ _ _ (by decide) (by rw [numeral_closed]; simp)]
      simp [subst_var]
    rw [← he]
    exact Beta.contract _ _ _
  exact .tail (.single (.app_left _ h₁)) h₂

/-- The reader returns the value component of the least successful stage. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The stage projections give the length and candidate value. Apply the finite-prefix proposition with the second accessor to obtain the list code, then use numerical pairing twice and query the first accessor. Every component computation terminates on every name. The reversed test therefore returns zero exactly at successful stages and one otherwise. At the least success, the search lemma with a result function reaches the second projection of that stage, which returns its candidate value. Confluence excludes a different numeral output. If there is no success, every reversed test returns one; the no-output part of the same search lemma excludes all numeral outputs. The two outer beta contractions of the reader preserve this conclusion by confluence.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For numerical input $n$, search all pairs $(N,v)$ in their numerical coding order. At each stage read the prefix
    $s=\restrict{p}{N}$ and query $r$ at the code of $(n,s,v)$. Return $v$ if the answer is nonzero, and continue otherwise.
    Each trial reads only finitely many input digits and makes one certificate query, so it terminates for every joined
    oracle. The prefix reader in §{sec:lambda-input-prefixes} produces the numerical list code of the first $N$ input values
    by appending one value at each recursion step. Its accessor may itself be a lambda term, so it also reads the second
    component of a joined name. Triple encoding, the two oracle projections, and the test use the numerical lambda terms
    already constructed. The uniform search lemma therefore gives a single closed lambda term, independent of $D$ and $F$.
    The explicit reader $\LambdaContinuousReader$ and its behavior on arbitrary joined names are proved in
    §{sec:lambda-continuous-reader}.
-/
theorem continuousReaderProgram_hit (w : ℕ → ℕ) (n : ℕ)
    (hex : ∃ k, continuousQuery w n k ≠ 0) :
    OracleRuns w continuousReaderProgram n (Nat.find hex).unpair.2 := by
  let j := Nat.find hex
  have hj : continuousQuery w n j ≠ 0 := Nat.find_spec hex
  have hbefore (k : ℕ) (hk : k < j) : continuousQuery w n k = 0 := by
    simpa using Nat.find_min hex hk
  apply (beta_steps_oracle (continuousReaderProgram_start n)).trans
  apply (resultSearchTerm_oracle_hit (continuousTest_input n)
    (by rw [numericalProjectionTerm_closed]; exact Finset.empty_subset _) j
    (by simpa only [ite_eq_right hj] using continuousTest_apply w n j)
    (fun k hk => ⟨0, by simpa only [hbefore k hk, ite_true] using continuousTest_apply w n k⟩)).trans
  exact beta_steps_oracle (numericalProjectionTerm_apply false j)

theorem continuousReaderProgram_domain (w : ℕ → ℕ) (n : ℕ) :
    (∃ m, OracleRuns w continuousReaderProgram n m) ↔ ∃ k, continuousQuery w n k ≠ 0 := by
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨k,hk⟩ := resultSearchTerm_oracle_output_requires_hit (continuousTest_input n)
      (by rw [numericalProjectionTerm_closed]; exact Finset.empty_subset _)
      (fun k => if continuousQuery w n k = 0 then 1 else 0) (continuousTest_apply w n)
      (oracle_numeral_after_reduction (beta_steps_oracle (continuousReaderProgram_start n)) hm)
    exact ⟨k,by simpa using hk⟩
  · intro hex
    exact ⟨_,continuousReaderProgram_hit w n hex⟩

/-- On arbitrary names, every numeral output is the value at the first hit. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Lambda reader for cylinder certificates
-/
theorem continuousReaderProgram_runs_iff (w : ℕ → ℕ) (n m : ℕ) :
    OracleRuns w continuousReaderProgram n m ↔
      ∃ h : ∃ k, continuousQuery w n k ≠ 0, m = (Nat.find h).unpair.2 := by
  constructor
  · intro hm
    have h := (continuousReaderProgram_domain w n).mp ⟨m,hm⟩
    exact ⟨h,hm.output_unique (continuousReaderProgram_hit w n h)⟩
  · rintro ⟨h,rfl⟩
    exact continuousReaderProgram_hit w n h

end NamedLambda.AlphaTerm
end PolishSpaceBook
