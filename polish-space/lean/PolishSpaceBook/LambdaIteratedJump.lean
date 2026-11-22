module

public import PolishSpaceBook.LambdaKleeneNotations
public import PolishSpaceBook.LambdaRelativeJump
public import PolishSpaceBook.LambdaRelativeComposition

@[expose] public section

/-! # Transfinite lambda jumps along Kleene notations

The recursion is on valid numerical notations. The relation of possible
stage values has exactly one set at each valid notation; choosing that unique
set asserts no computability of a notation-validity test. All reductions
between stages use closed lambda terms and finite beta/query derivations.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative

/-- Countable effective join, with the book's fixed numerical pairing. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{EffectiveJoin,IteratedJump}
    \end{mathmeta}
    For a sequence of sets $A_n\IncludedIn\NN$, its \termdefine{effective join} is
    $$\EffectiveJoin{n}{A_n}:=\{\NatPair{n}{m}:m\in A_n\}.$$
    We index the iteration by the notation itself. Fix a starting set $A\IncludedIn\NN$.
-/
def effectiveJoin (F : ℕ → Set ℕ) : Set ℕ := {z | z.unpair.2 ∈ F z.unpair.1}

theorem mem_effectiveJoin_pair (F : ℕ → Set ℕ) (n m : ℕ) :
    Nat.pair n m ∈ effectiveJoin F ↔ m ∈ F n := by simp [effectiveJoin]

/-- The three recursion rules, before choosing the unique value of a stage. -/
inductive JumpHierarchy (A : Set ℕ) : ℕ → Set ℕ → Prop
  | zero : JumpHierarchy A 1 A
  | succ {a : ℕ} {B : Set ℕ} (h : JumpHierarchy A a B) :
      JumpHierarchy A (successorCode a) (Jump (characteristic B))
  | limit (e : ℕ) (f : ℕ → ℕ) (hc : NumericalComputes (Term.closedProgram e) f)
      (hi : ∀ n, RawPrecedes (f n) (f (n+1))) (F : ℕ → Set ℕ)
      (hf : ∀ n, JumpHierarchy A (f n) (F n)) :
      JumpHierarchy A (limitCode e) (effectiveJoin F)

theorem JumpHierarchy.valid {A B : Set ℕ} {a : ℕ} (h : JumpHierarchy A a B) : Valid a := by
  induction h with
  | zero => exact .zero
  | succ h ih => exact .succ ih
  | limit e f hc hi F hf ih => exact .limit e f hc ih hi

theorem JumpHierarchy.cases_rule {A B : Set ℕ} {a : ℕ} (h : JumpHierarchy A a B) :
    (a = 1 ∧ B = A) ∨
    (∃ b D, a = successorCode b ∧ JumpHierarchy A b D ∧ B = Jump (characteristic D)) ∨
    (∃ e f, ∃ _ : NumericalComputes (Term.closedProgram e) f,
      (∀ n, RawPrecedes (f n) (f (n+1))) ∧
      ∃ F, a = limitCode e ∧ (∀ n, JumpHierarchy A (f n) (F n)) ∧ B = effectiveJoin F) := by
  cases h with
  | zero => exact Or.inl ⟨rfl,rfl⟩
  | @succ a B h => exact Or.inr (Or.inl ⟨a,B,rfl,h,rfl⟩)
  | limit e f hc hi F hf => exact Or.inr (Or.inr ⟨e,f,hc,hi,F,rfl,hf,rfl⟩)

private theorem successor_ne_one {a : ℕ} (ha : 0 < a) : successorCode a ≠ 1 := by
  intro h
  have he : successorCode a = successorCode 0 := h
  have := successorCode_injective he
  omega

private theorem limit_ne_one (e : ℕ) : limitCode e ≠ 1 := by
  have := limitCode_ge_three e
  omega

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For uniqueness, induct on a derivation of $(a,B)$ and compare any other derivation with the same first
    coordinate. The three numerical forms are disjoint, and both the successor and limit code functions are
    injective. Thus successor derivations have the same preceding notation, where the induction hypothesis
    identifies the sets. At a limit, the index $e$ is the same, and uniqueness of the output of $P_e$ identifies
    the two numerical sequences term by term. The induction hypotheses identify all their attached sets,
    so their joins agree. Assign the unique set to each notation. The rules give the displayed equations;
    induction on notation generation shows that any family satisfying them has these same values.
    \end{proof}
-/
theorem JumpHierarchy.unique {A B C : Set ℕ} {a : ℕ}
    (hB : JumpHierarchy A a B) (hC : JumpHierarchy A a C) : B = C := by
  induction hB generalizing C with
  | zero =>
    rcases hC.cases_rule with ⟨_,rfl⟩ | ⟨b,D,he,hD,_⟩ | ⟨e,f,hc,hi,F,he,hF,_⟩
    · rfl
    · exact (successor_ne_one hD.valid.pos he.symm).elim
    · exact (limit_ne_one e he.symm).elim
  | @succ a B h ih =>
    rcases hC.cases_rule with ⟨he,_⟩ | ⟨b,D,he,hD,rfl⟩ | ⟨e,f,hc,hi,F,he,hF,_⟩
    · exact (successor_ne_one h.valid.pos he).elim
    · have heq := successorCode_injective he
      subst b
      rw [ih hD]
    · exact (successorCode_ne_limitCode a e he).elim
  | limit e f hc hi F hf ih =>
    rcases hC.cases_rule with ⟨he,_⟩ | ⟨b,D,he,hD,_⟩ | ⟨e',g,hc',hi',G,he,hG,rfl⟩
    · exact (limit_ne_one e he).elim
    · exact (successorCode_ne_limitCode b e he.symm).elim
    · have heq := limitCode_injective he
      subst e'
      have hfg : f = g := funext (fun n => runs_unique (hc.2 n) (hc'.2 n))
      subst g
      exact congrArg effectiveJoin (funext (fun n => ih n (hG n)))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Generate pairs $(a,B)$ by these three rules: start with $(1,A)$; from $(a,B)$ form $(2^a,B')$;
    and, for a permitted limit sequence, join the sets attached to its terms. Induction on the generation of
    $a\in\KleeneO$ gives at least one such set $B$. At a limit, choose the sets whose existence is already
    established for all sequence terms and take their effective join.
-/
theorem Valid.exists_jumpHierarchy (A : Set ℕ) {a : ℕ} (ha : Valid a) :
    ∃ B, JumpHierarchy A a B := by
  induction ha with
  | zero => exact ⟨A,.zero⟩
  | succ ha ih => obtain ⟨B,hB⟩ := ih; exact ⟨_,.succ hB⟩
  | limit e f hc hf hi ih =>
    choose F hF using ih
    exact ⟨_,.limit e f hc hi F hF⟩

/-- Iteration starting from A, indexed by a valid notation rather than its ordinal value. -/
noncomputable def iteratedJump (A : Set ℕ) (a : ℕ) (ha : Valid a) : Set ℕ :=
  Classical.choose (ha.exists_jumpHierarchy A)

theorem iteratedJump_spec (A : Set ℕ) (a : ℕ) (ha : Valid a) :
    JumpHierarchy A a (iteratedJump A a ha) := Classical.choose_spec (ha.exists_jumpHierarchy A)

theorem iteratedJump_zero (A : Set ℕ) : iteratedJump A 1 .zero = A :=
  (iteratedJump_spec A 1 .zero).unique .zero

theorem iteratedJump_successor (A : Set ℕ) (a : ℕ) (ha : Valid a) :
    iteratedJump A (successorCode a) (.succ ha) = Jump (characteristic (iteratedJump A a ha)) :=
  (iteratedJump_spec A _ _).unique (.succ (iteratedJump_spec A a ha))

theorem iteratedJump_limit (A : Set ℕ) (e : ℕ) (f : ℕ → ℕ)
    (hc : NumericalComputes (Term.closedProgram e) f)
    (hf : ∀ n, Valid (f n)) (hi : ∀ n, RawPrecedes (f n) (f (n+1))) :
    iteratedJump A (limitCode e) (.limit e f hc hf hi) =
      effectiveJoin (fun n => iteratedJump A (f n) (hf n)) :=
  (iteratedJump_spec A _ _).unique (.limit e f hc hi _ (fun n => iteratedJump_spec A (f n) (hf n)))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Iteration along Kleene notations
-/
theorem iteratedJump_unique (A : Set ℕ) (H : ∀ a, Valid a → Set ℕ)
    (hz : H 1 .zero = A)
    (hs : ∀ a ha, H (successorCode a) (.succ ha) = Jump (characteristic (H a ha)))
    (hl : ∀ e f hc hf hi, H (limitCode e) (.limit e f hc hf hi) =
      effectiveJoin (fun n => H (f n) (hf n)))
    (a : ℕ) (ha : Valid a) : H a ha = iteratedJump A a ha := by
  induction ha with
  | zero => rw [hz,iteratedJump_zero]
  | succ ha ih => rw [hs _ ha,iteratedJump_successor _ _ ha,ih]
  | limit e f hc hf hi ih =>
    rw [hl e f hc hf hi,iteratedJump_limit A e f hc hf hi]
    exact congrArg effectiveJoin (funext ih)

/-- Read a fixed row of a joined characteristic name by one paired query. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A_n\IncludedIn\NN$ and put
    $$B:=\EffectiveJoin{n}{A_n}=\{\NatPair{n}{m}:m\in A_n\}.$$
    Thus $\chi_B(\NatPair{n}{m})=\chi_{A_n}(m)$, where each characteristic function takes values one and zero.
    Using the closed numerical-pairing term, define
    \begin{mathmeta}
      \define{LambdaJoinSection}
    \end{mathmeta}
    $$\LambdaJoinSection{n}:=\lambdaab{o}{\lambdaab{m}{o(\LambdaNumericPair\,\ChurchNumeral{n}\,m)}}.$$
    The numeral for the selected component is part of this finite term.
-/
def joinSectionProgram (n : ℕ) : AlphaTerm :=
  lam 1 (lam 2 (app (var 1) (app (app numericalPairTerm (numeral n)) (var 2))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    All variables are bound, and the pairing term and numeral are closed. Two beta contractions supply the input
    function and the numeral for $m$. Numerical pairing reduces the query argument to the numeral for
    $\NatPair{n}{m}$; one input-query step then returns its value under $\varepsilon$. With $\varepsilon=\chi_B$,
    the defining identity for the join gives the required component bit. This construction is independent of the
    sets in the sequence. It supplies the limit-step accessor for §{sec:edst-ordinal-notations}.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A_n\IncludedIn\NN$ and put
    $$B:=\EffectiveJoin{n}{A_n}=\{\NatPair{n}{m}:m\in A_n\}.$$
    Thus $\chi_B(\NatPair{n}{m})=\chi_{A_n}(m)$, where each characteristic function takes values one and zero.
    Using the closed numerical-pairing term, define
    \begin{mathmeta}
      \define{LambdaJoinSection}
    \end{mathmeta}
    $$\LambdaJoinSection{n}:=\lambdaab{o}{\lambdaab{m}{o(\LambdaNumericPair\,\ChurchNumeral{n}\,m)}}.$$
    The numeral for the selected component is part of this finite term.
-/
theorem joinSectionProgram_uniform (n : ℕ) :
    UniformNumericalComputes (joinSectionProgram n) (fun ε m => ε (Nat.pair n m)) := by
  refine ⟨?_,fun ε m => ?_⟩
  · unfold joinSectionProgram Closed
    simp only [fv_lam,fv_app,fv_var,(show (numeral n).fv = ∅ from numeral_closed n),
      (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed)]
    decide
  · have h₁ : Beta (app (joinSectionProgram n) (var 0))
        (lam 2 (app (var 0) (app (app numericalPairTerm (numeral n)) (var 2)))) := by
      have he : (lam 2 (app (var 1) (app (app numericalPairTerm (numeral n)) (var 2)))).subst 1 (var 0) =
          lam 2 (app (var 0) (app (app numericalPairTerm (numeral n)) (var 2))) := by
        rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
        simp [subst_app,subst_var,subst_closed _ _ _ numericalPairTerm_closed,
          subst_closed _ _ _ (numeral_closed n)]
      rw [← he]
      exact Beta.contract 1 _ _
    have h₂ : Beta
        (app (lam 2 (app (var 0) (app (app numericalPairTerm (numeral n)) (var 2)))) (numeral m))
        (app (var 0) (app (app numericalPairTerm (numeral n)) (numeral m))) := by
      have he : (app (var 0) (app (app numericalPairTerm (numeral n)) (var 2))).subst 2 (numeral m) =
          app (var 0) (app (app numericalPairTerm (numeral n)) (numeral m)) := by
        simp [subst_app,subst_var,subst_closed _ _ _ numericalPairTerm_closed,
          subst_closed _ _ _ (numeral_closed n)]
      rw [← he]
      exact Beta.contract 2 _ _
    exact ((Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
      (oracle_steps_app_right (var 0) (beta_steps_oracle (numericalPairTerm_apply n m)))).tail (.query _)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Reading a component of an effective join
-/
theorem joinSectionProgram_computes (F : ℕ → Set ℕ) (n : ℕ) :
    Computes (characteristic (effectiveJoin F)) (joinSectionProgram n) (characteristic (F n)) := by
  classical
  refine ⟨(joinSectionProgram_uniform n).1,fun m => ?_⟩
  simpa only [characteristic,effectiveJoin,Set.mem_ofPred_eq,Nat.unpair_pair,Encodable.encode_nat]
    using (joinSectionProgram_uniform n).2 (characteristic (effectiveJoin F)) m

/-- Substitution of a total lambda accessor changes the oracle. -/
theorem computation_trans {ε δ f : ℕ → ℕ} (hf : Computable ε f) (he : Computable δ ε) :
    Computable δ f := by
  obtain ⟨P,hP⟩ := hf
  obtain ⟨Q,hQ⟩ := he
  exact ⟨compositionProgram P Q,compositionProgram_closed hP.1 hQ.1,
    fun n => compositionProgram_runs hP.1 hQ.1 (hP.2 n) hQ.2⟩

theorem iteratedJump_computable_edge (A : Set ℕ) {a b : ℕ}
    (ha : Valid a) (hb : Valid b) (h : Edge a b) :
    Computable (characteristic (iteratedJump A b hb)) (characteristic (iteratedJump A a ha)) := by
  cases hb with
  | zero => exact (not_edge_zero a h).elim
  | @succ b hb =>
    have he := (edge_successor_iff a b hb.pos).mp h
    subst a
    rw [iteratedJump_successor]
    exact characteristic_computable_from_jump _
  | limit e f hc hf hi =>
    obtain ⟨n,he⟩ := (edge_limit_iff e f hc a).mp h
    subst a
    rw [iteratedJump_limit A e f hc hf hi]
    exact ⟨_,joinSectionProgram_computes _ n⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For a successor step, recover the old set from its jump by the index transformation in
    §{sec:lambda-relative-jump}. For a limit step from $\varphi_e(n)$ to $3\cdot5^e$, query the joined
    characteristic function at $\NatPair{n}{m}$ to recover the value at $m$ in the $n$th component.
    The closed row-reading term and its finite reduction are given in §{sec:lambda-relative-jump}.
    For a specified finite precedence chain, substitute these accessors successively into the programs.
    The composition theorem gives the forward computation.
-/
theorem iteratedJump_computable_of_raw (A : Set ℕ) {a b : ℕ}
    (ha : Valid a) (hb : Valid b) (h : RawPrecedes a b) :
    Computable (characteristic (iteratedJump A b hb)) (characteristic (iteratedJump A a ha)) := by
  induction h with
  | single h => exact iteratedJump_computable_edge A ha hb h
  | tail h he ih =>
    exact computation_trans (ih (hb.edge_down he)) (iteratedJump_computable_edge A _ hb he)

/-- Strictness at limits uses the next term of the increasing notation sequence. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For strictness, induct on the generation of $b$. The case $b=1$ has no predecessors. For any chain into
    $b$, let $c$ be its last predecessor. Either $a=c$, or the forward computation already proved recovers
    the set at $a$ from the set at $c$. A computation of the set at $b$ from the set at $a$ would therefore
    compute it from the set at $c$ as well. If $b=2^c$, this contradicts strictness of the ordinary jump.
    If $b=3\cdot5^e$, write $c=\varphi_e(n)$ and put $d=\varphi_e(n+1)$. The limit rule gives
    $\KleenePrecedes{c}{d}$. The induction hypothesis at $d$ excludes computation of the set at $d$ from
    the set at $c$. But the set at $d$ is a component of the join at $b$, so the assumed reverse computation,
    followed by its row reader, would do exactly that. This proves strictness also at limits.
    \end{proof}
-/
theorem iteratedJump_not_computable_of_raw (A : Set ℕ) {a b : ℕ}
    (ha : Valid a) (hb : Valid b) (h : RawPrecedes a b) :
    ¬ Computable (characteristic (iteratedJump A a ha)) (characteristic (iteratedJump A b hb)) := by
  induction hb generalizing a with
  | zero =>
    obtain ⟨c,hc,_⟩ := rawPrecedes_last h
    exact (not_edge_zero c hc).elim
  | @succ b hb _ih =>
    intro hrev
    obtain ⟨c,hc,hac⟩ := rawPrecedes_last h
    have he := (edge_successor_iff c b hb.pos).mp hc
    subst c
    rw [iteratedJump_successor A b hb] at hrev
    rcases hac with he | hab
    · subst a
      exact characteristic_jump_not_computable _ hrev
    · exact characteristic_jump_not_computable _
        (computation_trans hrev (iteratedJump_computable_of_raw A ha hb hab))
  | limit e f hc hf hi ih =>
    intro hrev
    obtain ⟨c,he,hac⟩ := rawPrecedes_last h
    obtain ⟨n,hcn⟩ := (edge_limit_iff e f hc c).mp he
    subst c
    have hnext := iteratedJump_computable_edge A (hf (n+1)) (Valid.limit e f hc hf hi)
      (Edge.limit e (n+1) (f (n+1)) (hc.2 (n+1)))
    have hnexta := computation_trans hnext hrev
    rcases hac with he | han
    · subst a
      exact ih (n+1) (hf n) (hi n) hnexta
    · exact ih (n+1) (hf n) (hi n)
        (computation_trans hnexta (iteratedJump_computable_of_raw A ha (hf n) han))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Strict increase along notations
-/
theorem iteratedJump_strict (A : Set ℕ) {a b : ℕ} (ha : Valid a) (hb : Valid b)
    (h : Precedes a b) :
    Computable (characteristic (iteratedJump A b hb)) (characteristic (iteratedJump A a ha)) ∧
    ¬ Computable (characteristic (iteratedJump A a ha)) (characteristic (iteratedJump A b hb)) :=
  ⟨iteratedJump_computable_of_raw A ha hb ((precedes_iff a b).mp h).1,
    iteratedJump_not_computable_of_raw A ha hb ((precedes_iff a b).mp h).1⟩

end KleeneNotation
end PolishSpaceBook
