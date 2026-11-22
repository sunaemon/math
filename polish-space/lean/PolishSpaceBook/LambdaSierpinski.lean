module

public import PolishSpaceBook.LambdaFiniteTrials
public import PolishSpaceBook.LambdaRealizers
public import PolishSpaceBook.SierpinskiNames

@[expose] public section

/-! # Sierpiński semidecision using only closed lambda programs -/
namespace PolishSpaceBook
set_option maxRecDepth 4096
open Set NamedLambda NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The bridge to TTE is concrete. If $X$ is a computable Polish space with Cauchy representation $\rho_X$, an effectively
    open subset of $X$ is one whose preimage under $\rho_X$ is $\lSigma^0_1$ in $\DomainOf{\rho_X}$.
-/
def SemidecidableFromNames {X : Type*} (δ : Representation X) (U : Set X) : Prop :=
  ∃ P : AlphaTerm, P.Closed ∧ ∀ p : δ.domain,
    (∃ m, OracleRuns p.val P 0 m) ↔ δ.toFun p ∈ U

namespace NamedLambda.AlphaTerm

def semidecisionNameProgram (e : ℕ) : AlphaTerm :=
  lam 40 (app (app (app finiteTrialTerm (var 40)) (numeral e)) (numeral 0))

theorem semidecisionNameProgram_closed (e : ℕ) : (semidecisionNameProgram e).Closed := by
  unfold semidecisionNameProgram Closed
  simp only [fv_lam, fv_app, fv_var,
    (show finiteTrialTerm.fv = ∅ from finiteTrialTerm_closed),
    (show (numeral e).fv = ∅ from numeral_closed e),
    (show (numeral 0).fv = ∅ from numeral_closed 0)]
  simp

theorem semidecisionNameProgram_runs (p : ℕ → ℕ) (e k : ℕ) :
    OracleRuns p (semidecisionNameProgram e) k (Term.finiteTrial p e 0 k) := by
  have hb : Beta (app (semidecisionNameProgram e) (var 0))
      (app (app (app finiteTrialTerm (var 0)) (numeral e)) (numeral 0)) := by
    simpa only [semidecisionNameProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ finiteTrialTerm_closed,
      subst_closed _ _ _ (numeral_closed e), subst_closed _ _ _ (numeral_closed 0)] using
      Beta.contract 40 (app (app (app finiteTrialTerm (var 40)) (numeral e)) (numeral 0)) (var 0)
  exact (Relation.ReflTransGen.single (.beta (.app_left _ hb))).trans
    (finiteTrialTerm_apply p e 0 k)

def digitTest (P O : AlphaTerm) : AlphaTerm :=
  lam 41 (app (app (app zeroTestTerm (app (app P O) (var 41))) (numeral 1)) (numeral 0))

theorem digitTest_fv {P : AlphaTerm} (hP : P.Closed) (O : AlphaTerm) :
    (digitTest P O).fv = O.fv.erase 41 := by
  simp only [digitTest, fv_lam, fv_app, fv_var,
    (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show P.fv = ∅ from hP),
    (show (numeral 0).fv = ∅ from numeral_closed 0),
    (show (numeral 1).fv = ∅ from numeral_closed 1)]
  simp

theorem digitTest_apply {P : AlphaTerm} (hP : P.Closed) (p q : ℕ → ℕ)
    (h : ∀ k, OracleRuns p P k (q k)) (k : ℕ) :
    Relation.ReflTransGen (OracleStep p) (app (digitTest P (var 0)) (numeral k))
      (numeral (if q k = 0 then 1 else 0)) := by
  have hb : Beta (app (digitTest P (var 0)) (numeral k))
      (app (app (app zeroTestTerm (app (app P (var 0)) (numeral k))) (numeral 1)) (numeral 0)) := by
    convert Beta.contract 41
      (app (app (app zeroTestTerm (app (app P (var 0)) (var 41))) (numeral 1)) (numeral 0))
      (numeral k) using 1 <;> try rfl
    simp [subst_app, subst_var, subst_closed _ _ _ hP,
      subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed 1), subst_closed _ _ _ (numeral_closed 0)]
  apply (Relation.ReflTransGen.single (.beta hb)).trans
  apply (oracle_steps_app_left (oracle_steps_app_left
    (oracle_steps_app_right zeroTestTerm (h k)) _) _).trans
  cases q k with
  | zero =>
    simp only [ite_true]
    exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | succ r =>
    simp only [Nat.succ_ne_zero, ite_false]
    exact beta_steps_oracle (branch_succ r _ _)

def digitSearchProgram (P : AlphaTerm) : AlphaTerm :=
  lam 40 (lam 42 (app (app resultSearchTerm (digitTest P (var 40))) identityProgram))

theorem digitSearchProgram_closed {P : AlphaTerm} (hP : P.Closed) :
    (digitSearchProgram P).Closed := by
  unfold digitSearchProgram Closed
  simp only [fv_lam, fv_app, digitTest_fv hP, fv_var,
    (show resultSearchTerm.fv = ∅ from resultSearchTerm_closed),
    (show identityProgram.fv = ∅ from identityProgram_closed)]
  decide

theorem digitSearchProgram_start {P : AlphaTerm} (hP : P.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (digitSearchProgram P) (var 0)) (numeral n))
      (app (app resultSearchTerm (digitTest P (var 0))) identityProgram) := by
  have h₁ : Beta (app (digitSearchProgram P) (var 0))
      (lam 42 (app (app resultSearchTerm (digitTest P (var 0))) identityProgram)) := by
    convert Beta.contract 40
      (lam 42 (app (app resultSearchTerm (digitTest P (var 40))) identityProgram)) (var 0) using 1 <;> try rfl
    simp [digitTest, subst_lam_fresh, subst_app, subst_var, fv_var,
      subst_closed _ _ _ hP, subst_closed _ _ _ resultSearchTerm_closed,
      subst_closed _ _ _ identityProgram_closed, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1)]
  have h₂ : Beta (app (lam 42 (app (app resultSearchTerm (digitTest P (var 0))) identityProgram)) (numeral n))
      (app (app resultSearchTerm (digitTest P (var 0))) identityProgram) := by
    convert Beta.contract 42
      (app (app resultSearchTerm (digitTest P (var 0))) identityProgram) (numeral n) using 1
    symm
    apply subst_not_free
    rw [fv_app, fv_app, resultSearchTerm_closed, identityProgram_closed, digitTest_fv hP, fv_var]
    decide
  exact .tail (.single (.app_left _ h₁)) h₂

/-- The first nonzero output digit is the exact search result. -/
theorem digitSearchProgram_runs_first {P : AlphaTerm} (hP : P.Closed) (p q : ℕ → ℕ)
    (h : ∀ k, OracleRuns p P k (q k)) (j : ℕ) (hj : q j ≠ 0)
    (hb : ∀ k < j, q k = 0) (n : ℕ) :
    OracleRuns p (digitSearchProgram P) n j := by
  have hG : (digitTest P (var 0)).fv ⊆ {0} := by rw [digitTest_fv hP,fv_var]; simp
  have hF : identityProgram.fv ⊆ {0} := identityProgram_closed.input_fv
  apply (beta_steps_oracle (p := p) (digitSearchProgram_start hP n)).trans
  apply (resultSearchTerm_oracle_hit hG hF j
    (by simpa only [hj,ite_false] using digitTest_apply hP p q h j)
    (fun k hk => ⟨0,by simpa only [hb k hk,ite_true] using digitTest_apply hP p q h k⟩)).trans
  apply Relation.ReflTransGen.single ∘ OracleStep.beta
  simpa only [identityProgram,subst_var,ite_true] using Beta.contract 1 (var 1) (numeral j)

theorem digitSearchProgram_domain {P : AlphaTerm} (hP : P.Closed) (p q : ℕ → ℕ)
    (h : ∀ k, OracleRuns p P k (q k)) (n : ℕ) :
    (∃ m, OracleRuns p (digitSearchProgram P) n m) ↔ ∃ k, q k ≠ 0 := by
  classical
  have hG : (digitTest P (var 0)).fv ⊆ {0} := by rw [digitTest_fv hP, fv_var]; simp
  have hF : identityProgram.fv ⊆ {0} := identityProgram_closed.input_fv
  have hs := beta_steps_oracle (p := p) (digitSearchProgram_start hP n)
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨k,hk⟩ := resultSearchTerm_oracle_output_requires_hit hG hF
      (fun k => if q k = 0 then 1 else 0) (digitTest_apply hP p q h)
      (oracle_numeral_after_reduction hs hm)
    exact ⟨k,by simpa using hk⟩
  · intro hex
    let j := Nat.find hex
    have hj : q j ≠ 0 := Nat.find_spec hex
    have hb (k : ℕ) (hk : k < j) : q k = 0 := by simpa using Nat.find_min hex hk
    refine ⟨j, hs.trans ?_⟩
    apply (resultSearchTerm_oracle_hit hG hF j
      (by simpa only [hj,ite_false] using digitTest_apply hP p q h j)
      (fun k hk => ⟨0,by simpa only [hb k hk,ite_true] using digitTest_apply hP p q h k⟩)).trans
    apply Relation.ReflTransGen.single ∘ OracleStep.beta
    simpa only [identityProgram, subst_var, ite_true] using Beta.contract 1 (var 1) (numeral j)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Every stage test terminates, so if a successful stage exists, take its least index. The reversed tests are positive at
    earlier stages and zero at that successful stage. The result-search lemma with input queries returns the identity
    applied to that index's
    numeral, hence the numeral itself. If there is no successful stage, all reversed tests are positive; the no-output part
    of the same lemma applies. These conclusions hold for arbitrary reduction orders.
-/
theorem digitSearchProgram_runs_iff {P : AlphaTerm} (hP : P.Closed) (p q : ℕ → ℕ)
    (h : ∀ k, OracleRuns p P k (q k)) (n m : ℕ) :
    OracleRuns p (digitSearchProgram P) n m ↔ q m ≠ 0 ∧ ∀ k < m, q k = 0 := by
  classical
  constructor
  · intro hm
    have hex := (digitSearchProgram_domain hP p q h n).mp ⟨m,hm⟩
    have hj : q (Nat.find hex) ≠ 0 := Nat.find_spec hex
    have hb (k : ℕ) (hk : k < Nat.find hex) : q k = 0 := by
      simpa using Nat.find_min hex hk
    have he := (digitSearchProgram_runs_first hP p q h (Nat.find hex) hj hb n).output_unique hm
    simpa only [he] using And.intro hj hb
  · rintro ⟨hj,hb⟩
    exact digitSearchProgram_runs_first hP p q h m hj hb n

end NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Sierpi\'nski semidecision criterion
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $P$ realize $\chi_U$, and let $q$ be its output name on a valid input name $p$. For a free input variable $o$, define
    $$G_o:=\lambdaab{k}{\LambdaZeroTest\,(Pok)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
    \qquad I:=\lambdaab{x}{x}.$$
    The closed program
    $$\lambdaab{o}{\lambdaab{n}{\LambdaResultSearch\,G_o\,I}}$$
    ignores $n$ and searches the output digits in order. Every digit is defined. If $j$ is the first nonzero digit, the test is positive before $j$ and zero at $j$, so the search returns $\ChurchNumeral{j}$. If all digits are zero, every stage continues and the search has no numeral output, by the result-search lemma in §{sec:lambda-input-universal-evaluation}. This last assertion includes arbitrary reduction orders, not just the displayed search order. Thus the program is a semidecider.

    Conversely, let $P_e$ be a semidecider. Use the closed program
    $$\lambdaab{o}{\LambdaFiniteTrial\,o\,\ChurchNumeral{e}\,\ChurchNumeral{0}}$$
    to produce the name whose $k$th digit is the numerical result of the $k$th finite trial. Every digit is defined, including when the semidecider has no output. A digit is nonzero exactly when that trial succeeds, and some trial succeeds exactly when $P_e$ has a numeral output on input zero. This name therefore represents $\chi_U(x)$ for every name of $x$. Both displayed constructions use fixed lambda terms and the given finite program or its index; neither chooses a program after the input name has been supplied. At the code level, the first construction inserts the supplied closed term into a fixed syntax template, and the second inserts the numeral for its syntax code. Syntax constructors and the numeral-code construction are primitive recursive, proving the asserted uniformity.
    \end{proof}
-/
theorem lambda_computable_sierpinski_iff {X : Type*} (δ : Representation X) (U : Set X) :
    HasComputableRealizer δ sierpinskiRepresentation (fun x => x ∈ U) ↔
      SemidecidableFromNames δ U := by
  constructor
  · rintro ⟨F, ⟨P,hP⟩, hF⟩
    obtain ⟨hc,hr⟩ := typeTwoComputes_iff_runs.mp hP
    refine ⟨digitSearchProgram P,digitSearchProgram_closed hc,fun p => ?_⟩
    rw [digitSearchProgram_domain hc p.val (F p).val (hr p) 0]
    exact Iff.of_eq (hF p)
  · rintro ⟨P,hP,h⟩
    obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
    let F : δ.domain → sierpinskiRepresentation.domain :=
      fun p => ⟨fun k => Term.finiteTrial p.val e 0 k, Set.mem_univ _⟩
    refine ⟨F,⟨semidecisionNameProgram e, typeTwoComputes_iff_runs.mpr
      ⟨semidecisionNameProgram_closed e, fun p k => semidecisionNameProgram_runs p.val e k⟩⟩,?_⟩
    intro p
    apply propext
    change (∃ k, Term.finiteTrial p.val e 0 k ≠ 0) ↔ δ.toFun p ∈ U
    rw [finiteTrial_positive_iff, he]
    exact h p

theorem SemidecidableFromNames.isOpen_preimage {X : Type*}
    {δ : Representation X} {U : Set X} (h : SemidecidableFromNames δ U) :
    IsOpen (δ.toFun ⁻¹' U) := by
  obtain ⟨F, hF, hf⟩ := (lambda_computable_sierpinski_iff δ U).mpr h
  have hcont := sierpinskiRepresentation_continuous.comp
    (hF.continuous.subtype_mk (fun p => (F p).property))
  have he : sierpinskiRepresentation.toFun ∘ F = (fun p => δ.toFun p ∈ U) := funext hf
  rw [he] at hcont
  exact continuous_Prop.mp hcont

theorem SemidecidableFromNames.isOpen {X : Type*} [TopologicalSpace X]
    {δ : Representation X} {U : Set X} (h : SemidecidableFromNames δ U)
    (hδ : Topology.IsQuotientMap δ.toFun) : IsOpen U :=
  hδ.isOpen_preimage.mp h.isOpen_preimage

end PolishSpaceBook
