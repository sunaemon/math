module

public import PolishSpaceBook.LambdaRealizerAbstraction

@[expose] public section

/-! # Concrete lambda trackers for the realizability preorder and Heyting operations -/
namespace PolishSpaceBook.LambdaIndexPCA

open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

abbrev Runs (P : AlphaTerm) (a b : ℕ) : Prop :=
  Relation.ReflTransGen Beta (app P (numeral a)) (numeral b)

def evalProgram (e : ℕ) : AlphaTerm := app outputSearchTerm (numeral e)

theorem evalProgram_closed (e : ℕ) : (evalProgram e).Closed :=
  closed_app outputSearchTerm_closed (numeral_closed e)

theorem evalProgram_runs_iff (e a b : ℕ) : Runs (evalProgram e) a b ↔ App e a b :=
  outputSearchTerm_runs_iff e a b

theorem composeProgram_closed {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed) :
    (numericalCompose F G).Closed := by
  unfold numericalCompose Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [hF, hG]
  simp

theorem composeProgram_runs {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed)
    {a b c : ℕ} (hg : Runs G a b) (hf : Runs F b c) :
    Runs (numericalCompose F G) a c := by
  have hs : Beta (app (numericalCompose F G) (numeral a)) (app F (app G (numeral a))) := by
    simpa only [numericalCompose, subst_app, subst_var, ite_true,
      subst_closed _ _ _ hF, subst_closed _ _ _ hG] using
      Beta.contract 40 (app F (app G (var 40))) (numeral a)
  exact (Relation.ReflTransGen.single hs).trans ((beta_steps_app_right F hg).trans hf)

theorem combineProgram_closed {B F G : AlphaTerm}
    (hB : B.Closed) (hF : F.Closed) (hG : G.Closed) :
    (numericalCombine B F G).Closed := by
  unfold numericalCombine Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [hB, hF, hG]
  simp

theorem combineProgram_runs {B F G : AlphaTerm}
    (hB : B.Closed) (hF : F.Closed) (hG : G.Closed) {a b c d : ℕ}
    (hf : Runs F a b) (hg : Runs G a c)
    (hb : Relation.ReflTransGen Beta (app (app B (numeral b)) (numeral c)) (numeral d)) :
    Runs (numericalCombine B F G) a d := by
  have hs : Beta (app (numericalCombine B F G) (numeral a))
      (app (app B (app F (numeral a))) (app G (numeral a))) := by
    simpa only [numericalCombine, subst_app, subst_var, ite_true,
      subst_closed _ _ _ hB, subst_closed _ _ _ hF, subst_closed _ _ _ hG] using
      Beta.contract 40 (app (app B (app F (var 40))) (app G (var 40))) (numeral a)
  exact (Relation.ReflTransGen.single hs).trans
    ((beta_steps_app (beta_steps_app_right B hf) hg).trans hb)

/-- Total syntax computation on a pair gives an outer program returning the code. -/
theorem exists_binary_code_factory {B : AlphaTerm} {body : ℕ → ℕ → ℕ}
    (hB : NumericalComputes B (fun z => body z.unpair.1 z.unpair.2)) :
    ∃ outer : ℕ → ℕ, (∃ R, NumericalComputes R outer) ∧
      ∀ e a, App (outer e) a (body e a) := by
  obtain ⟨H, hH⟩ := Quotient.exists_rep (curryNumerical B)
  have hH' : mk H = curryNumerical B := hH
  let outer (e : ℕ) := (Term.app H (Term.churchNumeral e)).code
  have hp (e : ℕ) : Term.closedProgram (outer e) = app (curryNumerical B) (numeral e) := by
    have hm : mk (Term.app H (Term.churchNumeral e)) = app (curryNumerical B) (numeral e) := by
      change app (mk H) (mk (Term.churchNumeral e)) = _
      rw [hH', Term.mk_churchNumeral]
    exact (closedProgram_code_of_closed _ (hm.symm ▸ closed_app
      (curryNumerical_closed hB.1) (numeral_closed e))).trans hm
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed, numeralCodeTerm_apply⟩
  refine ⟨outer, ⟨_, (numericalConstant_computes H.code).applicationCode hn⟩, ?_⟩
  intro e a
  unfold App
  rw [hp]
  exact (curryNumerical_apply hB.1 e a).trans
    (by simpa only [Nat.unpair_pair] using hB.2 (Nat.pair e a))

/-- Fixing the first member of a paired input delays the partial evaluation. -/
def curryBodyProgram (e a : ℕ) : AlphaTerm := lam 40
  (app (evalProgram e) (app (app numericalPairTerm (numeral a)) (var 40)))

theorem curryBodyProgram_closed (e a : ℕ) : (curryBodyProgram e a).Closed := by
  unfold curryBodyProgram Closed
  simp only [fv_lam, fv_app, fv_var,
    (show (evalProgram e).fv = ∅ from evalProgram_closed e),
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),
    (show (numeral a).fv = ∅ from numeral_closed a)]
  decide

theorem curryBodyProgram_runs_iff (e a b c : ℕ) :
    Runs (curryBodyProgram e a) b c ↔ App e (Nat.pair a b) c := by
  have hs : Beta (app (curryBodyProgram e a) (numeral b))
      (app (evalProgram e) (app (app numericalPairTerm (numeral a)) (numeral b))) := by
    simpa only [curryBodyProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ (evalProgram_closed e), subst_closed _ _ _ numericalPairTerm_closed,
      subst_closed _ _ _ (numeral_closed a)] using
      Beta.contract 40 (app (evalProgram e) (app (app numericalPairTerm (numeral a)) (var 40))) (numeral b)
  have hr := (Relation.ReflTransGen.single hs).trans
    (beta_steps_app_right (evalProgram e) (numericalPairTerm_apply a b))
  rw [← evalProgram_runs_iff e (Nat.pair a b) c]
  exact ⟨numeral_after_reduction hr, fun h => hr.trans h⟩

def curryBodySyntax (U P : Term) (e a : ℕ) : Term := .lam 40
  (.app (.app U (Term.churchNumeral e))
    (.app (.app P (Term.churchNumeral a)) (.var 40)))

theorem curryBodySyntax_mk (U P : Term) (hU : mk U = outputSearchTerm)
    (hP : mk P = numericalPairTerm) (e a : ℕ) :
    mk (curryBodySyntax U P e a) = curryBodyProgram e a := by
  change lam 40 (app (app (mk U) (mk (Term.churchNumeral e)))
    (app (app (mk P) (mk (Term.churchNumeral a))) (var 40))) = _
  rw [hU, hP, Term.mk_churchNumeral, Term.mk_churchNumeral]
  rfl

theorem curryBodyCode_computes (U P : Term) :
    ∃ B, NumericalComputes B (fun z => (curryBodySyntax U P z.unpair.1 z.unpair.2).code) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed, numeralCodeTerm_apply⟩
  have hu := (numericalConstant_computes U.code).applicationCode (hn.comp (projection_computes true))
  have hp := ((numericalConstant_computes P.code).applicationCode
    (hn.comp (projection_computes false))).applicationCode (numericalConstant_computes (Term.var 40).code)
  exact ⟨_, (hu.applicationCode hp).abstractionCode 40⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For implication, suppose $e$ tracks $\theta\land\varphi\le\psi$. Fix named representatives of $U$ and numerical
    pairing and form the syntax code
    $$c(e,a)=\LambdaSyntaxCode{\lambda b.\,U\ChurchNumeral{e}(\LambdaNumericPair\,\ChurchNumeral{a}b)}.$$
    Numeral-code, application-code, and abstraction-code programs give a closed total program $C$ computing $c$ on paired
    inputs. Put
    $$H=\lambda e.\lambda a.\,C(\LambdaNumericPair\,e\,a),\qquad
    q(e)=\LambdaSyntaxCode{H\ChurchNumeral{e}},$$
    using a fixed named representative of $H$. The code map $q$ is also computed by a total lambda program. For every
    $e,a$, the application $q(e)\cdot a$ returns $c(e,a)$ without evaluating the program with that code. Moreover,
    $$c(e,a)\cdot b\simeq e\cdot\NatPair{a}{b}.$$
    Indeed, one beta contraction supplies $b$, numerical pairing computes $\NatPair{a}{b}$, and the universal evaluator
    has exactly the numerical outputs of the indexed program. Confluence gives the converse direction as well.
    Consequently $q(e)$ tracks $\theta\le(\varphi\to\psi)$. This remains valid when $\varphi(i)$ is empty: the code
    $c(e,a)$ is still returned, and its membership in the implication imposes no computations on inputs from that empty set.
-/
theorem exists_computable_curry_indices :
    ∃ (outer : ℕ → ℕ) (body : ℕ → ℕ → ℕ),
      (∃ R, NumericalComputes R outer) ∧
      (∃ B, NumericalComputes B (fun z => body z.unpair.1 z.unpair.2)) ∧
      (∀ e a, App (outer e) a (body e a)) ∧
      ∀ e a b c, App (body e a) b c ↔ App e (Nat.pair a b) c := by
  obtain ⟨U, hU⟩ := Quotient.exists_rep outputSearchTerm
  obtain ⟨P, hP⟩ := Quotient.exists_rep numericalPairTerm
  have hU' : mk U = outputSearchTerm := hU
  have hP' : mk P = numericalPairTerm := hP
  obtain ⟨B, hB⟩ := curryBodyCode_computes U P
  obtain ⟨outer, houter, hrun⟩ := exists_binary_code_factory (body := fun e a => (curryBodySyntax U P e a).code) hB
  refine ⟨outer, (fun e a => (curryBodySyntax U P e a).code), houter, ⟨B, hB⟩, hrun, ?_⟩
  intro e a b c
  have hm := curryBodySyntax_mk U P hU' hP' e a
  have hp := (closedProgram_code_of_closed _ (hm.symm ▸ curryBodyProgram_closed e a)).trans hm
  unfold App
  rw [hp]
  exact curryBodyProgram_runs_iff e a b c

/-- This notation fixes the concrete application graph, not an abstract hypothesis. -/
abbrev Reduces {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) : Prop :=
  RealizabilityReducible realizerAbstraction φ ψ

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    For a set $I$, a \termdefine{realizability predicate} on $I$ is a function
    $$\varphi:I\to\PowerSet{\NN}.$$
    Read $a\in\varphi(i)$ as "$a$ realizes that $\varphi$ holds at $i$." Predicates are ordered by uniform reducibility:
    $$
    \varphi\le\psi
    \quad\Longleftrightarrow\quad
    \exists e\in\NN\;\forall i\in I\;\forall a\in\varphi(i)\;
    e\cdot a\downarrow\in\psi(i).
    $$
    The witness $e$ is a single recursive operation converting every realizer of $\varphi(i)$ into a realizer of $\psi(i)$,
    uniformly in $i$.
-/
theorem reduces_iff {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    Reduces φ ψ ↔ ∃ e, ∀ i a, a ∈ φ i → ∃ b, App e a b ∧ b ∈ ψ i := by
  unfold Reduces RealizabilityReducible
  rw [realizerAbstraction_app]

theorem reduces_refl {I : Type*} (φ : RealizabilityPredicate ℕ I) : Reduces φ φ := by
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ numericalIdentity_computes.1
  rw [reduces_iff]
  refine ⟨e, fun i a ha => ⟨a, ?_, ha⟩⟩
  unfold App
  rw [he]
  exact numericalIdentity_computes.2 a

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $U=\LambdaOutputSearch$ for the universal evaluation term and $\pi_i=\LambdaNumericProjection{i}$ for the
    numerical projections. An index of $\lambda a.a$ tracks reflexivity. If $e$ tracks $\varphi\le\psi$ and $f$ tracks
    $\psi\le\theta$, an index of
    $$\lambda a.\,U\ChurchNumeral{f}(U\ChurchNumeral{e}a)$$
    tracks $\varphi\le\theta$: first run the $e$ computation, then the $f$ computation. The same index works for every
    point of the base set. Thus reducibility is transitive. Reindexing changes only the base point in the membership
    conditions, so it keeps the original tracker.
-/
theorem reduces_trans {I : Type*} {φ ψ θ : RealizabilityPredicate ℕ I}
    (h₁ : Reduces φ ψ) (h₂ : Reduces ψ θ) : Reduces φ θ := by
  obtain ⟨e, he⟩ := (reduces_iff φ ψ).mp h₁
  obtain ⟨f, hf⟩ := (reduces_iff ψ θ).mp h₂
  obtain ⟨c, hc⟩ := Term.closedProgram_surjective _
    (composeProgram_closed (evalProgram_closed f) (evalProgram_closed e))
  rw [reduces_iff]
  refine ⟨c, ?_⟩
  intro i a ha
  obtain ⟨b, hb, hbψ⟩ := he i a ha
  obtain ⟨d, hd, hdθ⟩ := hf i b hbψ
  refine ⟨d, ?_, hdθ⟩
  unfold App
  rw [hc]
  exact composeProgram_runs (evalProgram_closed f) (evalProgram_closed e)
    ((evalProgram_runs_iff e a b).mpr hb) ((evalProgram_runs_iff f b d).mpr hd)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The Heyting operations are the realizability clauses for intuitionistic logic:
    $$
    \top(i)=\NN,\qquad \bot(i)=\emptyset,
    $$
    $$
    (\varphi\land\psi)(i)=\{\langle a,b\rangle:a\in\varphi(i),\ b\in\psi(i)\},
    $$
    $$
    (\varphi\lor\psi)(i)=
    \{\langle 0,a\rangle:a\in\varphi(i)\}
    \cup
    \{\langle 1,b\rangle:b\in\psi(i)\},
    $$
    and
    $$
    (\varphi\to\psi)(i)=
    \{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
    $$
-/
def realizabilityAnd {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) : RealizabilityPredicate ℕ I :=
  fun i => {z | z.unpair.1 ∈ φ i ∧ z.unpair.2 ∈ ψ i}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The Heyting operations are the realizability clauses for intuitionistic logic:
    $$
    \top(i)=\NN,\qquad \bot(i)=\emptyset,
    $$
    $$
    (\varphi\land\psi)(i)=\{\langle a,b\rangle:a\in\varphi(i),\ b\in\psi(i)\},
    $$
    $$
    (\varphi\lor\psi)(i)=
    \{\langle 0,a\rangle:a\in\varphi(i)\}
    \cup
    \{\langle 1,b\rangle:b\in\psi(i)\},
    $$
    and
    $$
    (\varphi\to\psi)(i)=
    \{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
    $$
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The effective topos is intuitionistic for a different reason. Its truth values are not opens in a space of conditions;
    they are sets of realizers. A proof of $\varphi\lor\psi$ must choose a side and provide evidence for it. A proof of
    $\varphi\to\psi$ must be a computable transformer from realizers of $\varphi$ to realizers of $\psi$. Excluded middle
    would require a uniform algorithm deciding which side of every proposition has evidence, and the halting problem blocks
    such a uniform decision.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    *   a proof of $\varphi\land\psi$ is a pair of realizers;
    *   a proof of $\varphi\lor\psi$ is a tag and a realizer for the chosen side;
    *   a proof of $\varphi\to\psi$ is an index transforming realizers of $\varphi$ into realizers of $\psi$;
    *   a realizer of $\exists x\,\varphi(x)$ lies in the union of the realizer sets over possible witnesses,
        with existence evidence included when quantifying over a PER object. It need not encode an arbitrary
        base-set witness as a natural number.
-/
def realizabilityImp {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) : RealizabilityPredicate ℕ I :=
  fun i => {e | ∀ a, a ∈ φ i → ∃ b, App e a b ∧ b ∈ ψ i}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The Heyting operations are the realizability clauses for intuitionistic logic:
    $$
    \top(i)=\NN,\qquad \bot(i)=\emptyset,
    $$
    $$
    (\varphi\land\psi)(i)=\{\langle a,b\rangle:a\in\varphi(i),\ b\in\psi(i)\},
    $$
    $$
    (\varphi\lor\psi)(i)=
    \{\langle 0,a\rangle:a\in\varphi(i)\}
    \cup
    \{\langle 1,b\rangle:b\in\psi(i)\},
    $$
    and
    $$
    (\varphi\to\psi)(i)=
    \{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
    $$
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    *   a proof of $\varphi\land\psi$ is a pair of realizers;
    *   a proof of $\varphi\lor\psi$ is a tag and a realizer for the chosen side;
    *   a proof of $\varphi\to\psi$ is an index transforming realizers of $\varphi$ into realizers of $\psi$;
    *   a realizer of $\exists x\,\varphi(x)$ lies in the union of the realizer sets over possible witnesses,
        with existence evidence included when quantifying over a PER object. It need not encode an arbitrary
        base-set witness as a natural number.
-/
theorem realizabilityAnd_mem_iff {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) (i : I) (z : ℕ) :
    z ∈ realizabilityAnd φ ψ i ↔ ∃ a ∈ φ i, ∃ b ∈ ψ i, z = Nat.pair a b := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨z.unpair.1, ha, z.unpair.2, hb, (Nat.pair_unpair z).symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa only [realizabilityAnd, Set.mem_ofPred_eq, Nat.unpair_pair] using And.intro ha hb

theorem reduces_and_left {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    Reduces (realizabilityAnd φ ψ) φ := by
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ (projection_computes true).1
  rw [reduces_iff]
  refine ⟨e, fun i z hz => ⟨z.unpair.1, ?_, hz.1⟩⟩
  unfold App
  rw [he]
  exact (projection_computes true).2 z

theorem reduces_and_right {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    Reduces (realizabilityAnd φ ψ) ψ := by
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ (projection_computes false).1
  rw [reduces_iff]
  refine ⟨e, fun i z hz => ⟨z.unpair.2, ?_, hz.2⟩⟩
  unfold App
  rw [he]
  exact (projection_computes false).2 z

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The indices of $\pi_1$ and $\pi_2$ track the two projections from $\varphi\land\psi$.
    If $e,f$ track $\theta\le\varphi$ and $\theta\le\psi$, respectively, use an index of
    $$\lambda a.\,\LambdaNumericPair\,(U\ChurchNumeral{e}a)(U\ChurchNumeral{f}a).$$
    Both computations terminate on every realizer of $\theta$, so this term returns a pair realizing $\varphi\land\psi$.
    Composing with the two projections proves the converse.
-/
theorem reduces_and_intro {I : Type*} {θ φ ψ : RealizabilityPredicate ℕ I}
    (hφ : Reduces θ φ) (hψ : Reduces θ ψ) : Reduces θ (realizabilityAnd φ ψ) := by
  obtain ⟨e, he⟩ := (reduces_iff θ φ).mp hφ
  obtain ⟨f, hf⟩ := (reduces_iff θ ψ).mp hψ
  obtain ⟨p, hp⟩ := Term.closedProgram_surjective _
    (combineProgram_closed numericalPairTerm_closed (evalProgram_closed e) (evalProgram_closed f))
  rw [reduces_iff]
  refine ⟨p, ?_⟩
  intro i a ha
  obtain ⟨b, hb, hbφ⟩ := he i a ha
  obtain ⟨c, hc, hcψ⟩ := hf i a ha
  refine ⟨Nat.pair b c, ?_, ?_⟩
  · unfold App
    rw [hp]
    exact combineProgram_runs numericalPairTerm_closed (evalProgram_closed e) (evalProgram_closed f)
      ((evalProgram_runs_iff e a b).mpr hb) ((evalProgram_runs_iff f a c).mpr hc)
      (numericalPairTerm_apply b c)
  · simpa only [realizabilityAnd, Set.mem_ofPred_eq, Nat.unpair_pair] using And.intro hbφ hcψ

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
theorem reduces_and_iff {I : Type*} (θ φ ψ : RealizabilityPredicate ℕ I) :
    Reduces θ (realizabilityAnd φ ψ) ↔ Reduces θ φ ∧ Reduces θ ψ :=
  ⟨fun h => ⟨reduces_trans h (reduces_and_left φ ψ), reduces_trans h (reduces_and_right φ ψ)⟩,
    fun h => reduces_and_intro h.1 h.2⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Conversely, if $e$ tracks $\theta\le(\varphi\to\psi)$, take an index of
    $$\lambda z.\,U\bigl(U\ChurchNumeral{e}(\pi_1z)\bigr)(\pi_2z).$$
    On an input $\NatPair{a}{b}$ realizing $\theta\land\varphi$, first compute the implication realizer $e\cdot a$,
    then apply it to $b$. Both computations are defined by the tracking assumptions, and the final result belongs to
    $\psi(i)$. This proves the implication adjunction using the same numerical application as all the other clauses.
    \end{proof}
-/
theorem reduces_imp_iff {I : Type*} (θ φ ψ : RealizabilityPredicate ℕ I) :
    Reduces (realizabilityAnd θ φ) ψ ↔ Reduces θ (realizabilityImp φ ψ) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := (reduces_iff _ _).mp h
    obtain ⟨outer, body, _, _, hout, hbody⟩ := exists_computable_curry_indices
    rw [reduces_iff]
    refine ⟨outer e, fun i a ha => ⟨body e a, hout e a, ?_⟩⟩
    intro b hb
    obtain ⟨c, hc, hcψ⟩ := he i (Nat.pair a b)
      (by simpa only [realizabilityAnd, Set.mem_ofPred_eq, Nat.unpair_pair] using And.intro ha hb)
    exact ⟨c, (hbody e a b c).mpr hc, hcψ⟩
  · intro h
    obtain ⟨e, he⟩ := (reduces_iff _ _).mp h
    let F := numericalCompose (evalProgram e) (numericalProjectionTerm true)
    have hF : F.Closed := composeProgram_closed (evalProgram_closed e) (projection_computes true).1
    obtain ⟨u, hu⟩ := Term.closedProgram_surjective _
      (combineProgram_closed outputSearchTerm_closed hF (projection_computes false).1)
    rw [reduces_iff]
    refine ⟨u, ?_⟩
    intro i z hz
    obtain ⟨b, hb, hbimp⟩ := he i z.unpair.1 hz.1
    obtain ⟨c, hc, hcψ⟩ := hbimp z.unpair.2 hz.2
    refine ⟨c, ?_, hcψ⟩
    unfold App
    rw [hu]
    apply combineProgram_runs outputSearchTerm_closed hF (projection_computes false).1
      (composeProgram_runs (evalProgram_closed e) (projection_computes true).1
        ((projection_computes true).2 z) ((evalProgram_runs_iff e z.unpair.1 b).mpr hb))
      ((projection_computes false).2 z)
    exact (outputSearchTerm_runs_iff b z.unpair.2 c).mpr hc


def caseProgram (F G : AlphaTerm) : AlphaTerm := lam 40
  (app (app (app zeroTestTerm (app (numericalProjectionTerm true) (var 40)))
    (app F (app (numericalProjectionTerm false) (var 40))))
    (app G (app (numericalProjectionTerm false) (var 40))))

theorem caseProgram_closed {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed) :
    (caseProgram F G).Closed := by
  unfold caseProgram Closed
  simp only [fv_lam, fv_app, fv_var,
    (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed),
    (show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1),
    (show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1)]
  rw [hF, hG]
  decide

theorem caseProgram_start {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed) (tag n : ℕ) :
    Relation.ReflTransGen Beta (app (caseProgram F G) (numeral (Nat.pair tag n)))
      (app (app (app zeroTestTerm (numeral tag)) (app F (numeral n))) (app G (numeral n))) := by
  let z := numeral (Nat.pair tag n)
  have hs : Beta (app (caseProgram F G) z)
      (app (app (app zeroTestTerm (app (numericalProjectionTerm true) z))
        (app F (app (numericalProjectionTerm false) z)))
        (app G (app (numericalProjectionTerm false) z))) := by
    simpa only [caseProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ hF, subst_closed _ _ _ hG,
      subst_closed _ _ _ (projection_computes true).1,
      subst_closed _ _ _ (projection_computes false).1] using
      Beta.contract 40 (app (app (app zeroTestTerm (app (numericalProjectionTerm true) (var 40)))
        (app F (app (numericalProjectionTerm false) (var 40))))
        (app G (app (numericalProjectionTerm false) (var 40)))) z
  have hl : Runs (numericalProjectionTerm true) (Nat.pair tag n) tag := by
    simpa using (projection_computes true).2 (Nat.pair tag n)
  have hr : Runs (numericalProjectionTerm false) (Nat.pair tag n) n := by
    simpa using (projection_computes false).2 (Nat.pair tag n)
  exact (Relation.ReflTransGen.single hs).trans
    (beta_steps_app (beta_steps_app (beta_steps_app_right zeroTestTerm hl)
      (beta_steps_app_right F hr)) (beta_steps_app_right G hr))

theorem caseProgram_left {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed)
    {a b : ℕ} (h : Runs F a b) : Runs (caseProgram F G) (Nat.pair 0 a) b := by
  have hc : 2 ∉ (app F (numeral a)).fv := by
    rw [closed_app hF (numeral_closed a)]
    simp
  exact (caseProgram_start hF hG 0 a).trans
    ((branch_zero _ _ hc).trans h)

theorem caseProgram_right {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed)
    {a b : ℕ} (h : Runs G a b) : Runs (caseProgram F G) (Nat.pair 1 a) b :=
  (caseProgram_start hF hG 1 a).trans ((branch_succ 0 _ _).trans h)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The Heyting operations are the realizability clauses for intuitionistic logic:
    $$
    \top(i)=\NN,\qquad \bot(i)=\emptyset,
    $$
    $$
    (\varphi\land\psi)(i)=\{\langle a,b\rangle:a\in\varphi(i),\ b\in\psi(i)\},
    $$
    $$
    (\varphi\lor\psi)(i)=
    \{\langle 0,a\rangle:a\in\varphi(i)\}
    \cup
    \{\langle 1,b\rangle:b\in\psi(i)\},
    $$
    and
    $$
    (\varphi\to\psi)(i)=
    \{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
    $$
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The effective topos is intuitionistic for a different reason. Its truth values are not opens in a space of conditions;
    they are sets of realizers. A proof of $\varphi\lor\psi$ must choose a side and provide evidence for it. A proof of
    $\varphi\to\psi$ must be a computable transformer from realizers of $\varphi$ to realizers of $\psi$. Excluded middle
    would require a uniform algorithm deciding which side of every proposition has evidence, and the halting problem blocks
    such a uniform decision.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    *   a proof of $\varphi\land\psi$ is a pair of realizers;
    *   a proof of $\varphi\lor\psi$ is a tag and a realizer for the chosen side;
    *   a proof of $\varphi\to\psi$ is an index transforming realizers of $\varphi$ into realizers of $\psi$;
    *   a realizer of $\exists x\,\varphi(x)$ lies in the union of the realizer sets over possible witnesses,
        with existence evidence included when quantifying over a PER object. It need not encode an arbitrary
        base-set witness as a natural number.
-/
def realizabilityOr {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) : RealizabilityPredicate ℕ I :=
  fun i => {z | (∃ a ∈ φ i, z = Nat.pair 0 a) ∨ (∃ b ∈ ψ i, z = Nat.pair 1 b)}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The Heyting operations are the realizability clauses for intuitionistic logic:
    $$
    \top(i)=\NN,\qquad \bot(i)=\emptyset,
    $$
    $$
    (\varphi\land\psi)(i)=\{\langle a,b\rangle:a\in\varphi(i),\ b\in\psi(i)\},
    $$
    $$
    (\varphi\lor\psi)(i)=
    \{\langle 0,a\rangle:a\in\varphi(i)\}
    \cup
    \{\langle 1,b\rangle:b\in\psi(i)\},
    $$
    and
    $$
    (\varphi\to\psi)(i)=
    \{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
    $$
-/
def realizabilityTop (I : Type*) : RealizabilityPredicate ℕ I := fun _ => Set.univ
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The Heyting operations are the realizability clauses for intuitionistic logic:
    $$
    \top(i)=\NN,\qquad \bot(i)=\emptyset,
    $$
    $$
    (\varphi\land\psi)(i)=\{\langle a,b\rangle:a\in\varphi(i),\ b\in\psi(i)\},
    $$
    $$
    (\varphi\lor\psi)(i)=
    \{\langle 0,a\rangle:a\in\varphi(i)\}
    \cup
    \{\langle 1,b\rangle:b\in\psi(i)\},
    $$
    and
    $$
    (\varphi\to\psi)(i)=
    \{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
    $$
-/
def realizabilityBot (I : Type*) : RealizabilityPredicate ℕ I := fun _ => ∅

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
theorem reduces_top {I : Type*} (φ : RealizabilityPredicate ℕ I) :
    Reduces φ (realizabilityTop I) := by
  obtain ⟨e, he⟩ := (reduces_iff φ φ).mp (reduces_refl φ)
  rw [reduces_iff]
  exact ⟨e, fun i a ha => let ⟨b, hb, _⟩ := he i a ha; ⟨b, hb, Set.mem_univ b⟩⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
theorem bot_reduces {I : Type*} (φ : RealizabilityPredicate ℕ I) :
    Reduces (realizabilityBot I) φ := by
  rw [reduces_iff]
  exact ⟨0, fun _ _ h => False.elim h⟩

theorem reduces_or_left {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    Reduces φ (realizabilityOr φ ψ) := by
  have h := (numericalConstant_computes 0).pair numericalIdentity_computes
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ h.1
  rw [reduces_iff]
  refine ⟨e, fun i a ha => ⟨Nat.pair 0 a, ?_, Or.inl ⟨a, ha, rfl⟩⟩⟩
  unfold App
  rw [he]
  exact h.2 a

theorem reduces_or_right {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    Reduces ψ (realizabilityOr φ ψ) := by
  have h := (numericalConstant_computes 1).pair numericalIdentity_computes
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ h.1
  rw [reduces_iff]
  refine ⟨e, fun i a ha => ⟨Nat.pair 1 a, ?_, Or.inr ⟨a, ha, rfl⟩⟩⟩
  unfold App
  rw [he]
  exact h.2 a

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The injections into $\varphi\lor\psi$ are tracked by indices of
    $$\lambda a.\,\LambdaNumericPair\,\ChurchNumeral{0}a,
    \qquad\lambda b.\,\LambdaNumericPair\,\ChurchNumeral{1}b.$$
    If $e,f$ track $\varphi\le\theta$ and $\psi\le\theta$, use an index of
    $$\lambda z.\,\LambdaZeroTest(\pi_1z)
      (U\ChurchNumeral{e}(\pi_2z))(U\ChurchNumeral{f}(\pi_2z)).$$
    On a realizer of $\varphi\lor\psi$, the tag is $0$ or $1$. The zero test selects the corresponding branch before
    that branch is evaluated; the unused computation need not terminate. The selected computation returns a realizer
    of $\theta$. Composing with the two injections proves the converse. The identity index tracks $\varphi\le\top$.
    For $\bot\le\varphi$, any index works because there are no input realizers.
-/
theorem or_reduces {I : Type*} {φ ψ θ : RealizabilityPredicate ℕ I}
    (hφ : Reduces φ θ) (hψ : Reduces ψ θ) : Reduces (realizabilityOr φ ψ) θ := by
  obtain ⟨e, he⟩ := (reduces_iff _ _).mp hφ
  obtain ⟨f, hf⟩ := (reduces_iff _ _).mp hψ
  obtain ⟨c, hc⟩ := Term.closedProgram_surjective _
    (caseProgram_closed (evalProgram_closed e) (evalProgram_closed f))
  rw [reduces_iff]
  refine ⟨c, ?_⟩
  intro i z hz
  rcases hz with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · obtain ⟨b, hb, hbθ⟩ := he i a ha
    refine ⟨b, ?_, hbθ⟩
    unfold App
    rw [hc]
    exact caseProgram_left (evalProgram_closed e) (evalProgram_closed f)
      ((evalProgram_runs_iff e a b).mpr hb)
  · obtain ⟨b, hb, hbθ⟩ := hf i a ha
    refine ⟨b, ?_, hbθ⟩
    unfold App
    rw [hc]
    exact caseProgram_right (evalProgram_closed e) (evalProgram_closed f)
      ((evalProgram_runs_iff f a b).mpr hb)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
theorem or_reduces_iff {I : Type*} (φ ψ θ : RealizabilityPredicate ℕ I) :
    Reduces (realizabilityOr φ ψ) θ ↔ Reduces φ θ ∧ Reduces ψ θ :=
  ⟨fun h => ⟨reduces_trans (reduces_or_left φ ψ) h, reduces_trans (reduces_or_right φ ψ) h⟩,
    fun h => or_reduces h.1 h.2⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
@[reducible] def realizabilityPreorder (I : Type*) : Preorder (RealizabilityPredicate ℕ I) where
  le := Reduces
  lt := fun φ ψ => Reduces φ ψ ∧ ¬Reduces ψ φ
  le_refl := reduces_refl
  le_trans _ _ _ := reduces_trans

/-- Reindexing uses exactly the same program index. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: realizability propositional operations
-/
theorem reindex_reduces {I J : Type*} (f : I → J) {φ ψ : RealizabilityPredicate ℕ J}
    (h : Reduces φ ψ) : Reduces (realizabilityReindex f φ) (realizabilityReindex f ψ) := by
  obtain ⟨e, he⟩ := (reduces_iff _ _).mp h
  rw [reduces_iff]
  exact ⟨e, fun i a ha => he (f i) a ha⟩

end PolishSpaceBook.LambdaIndexPCA
