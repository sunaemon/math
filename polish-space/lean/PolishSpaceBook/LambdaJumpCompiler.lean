module

public import PolishSpaceBook.LambdaJumpQuantifiers

@[expose] public section

/-! # Computable index transformations for numerical quantifiers

All code families below are functions into the existing named lambda syntax.
Application and abstraction code constructors compute them. Representatives
of fixed library terms are chosen once, before any index or input function.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private def SyntaxComputable (T : ℕ → Term) : Prop :=
  ∃ F, NumericalComputes F (fun e => (T e).code)

private theorem syntax_const (P : Term) : SyntaxComputable (fun _ => P) :=
  ⟨numericalConstant P.code,numericalConstant_computes P.code⟩

private theorem syntax_app {P Q : ℕ → Term} (hP : SyntaxComputable P) (hQ : SyntaxComputable Q) :
    SyntaxComputable (fun e => .app (P e) (Q e)) := by
  obtain ⟨F,hF⟩ := hP
  obtain ⟨G,hG⟩ := hQ
  exact ⟨codeTagProgram 1 F G,codeTagProgram_computes hF hG 1⟩

private theorem syntax_lam {P : ℕ → Term} (hP : SyntaxComputable P) (x : ℕ) :
    SyntaxComputable (fun e => .lam x (P e)) := by
  obtain ⟨F,hF⟩ := hP
  exact ⟨codeTagProgram 2 (numericalConstant x) F,
    codeTagProgram_computes (numericalConstant_computes x) hF 2⟩

private theorem syntax_numeral {f : ℕ → ℕ} {F : AlphaTerm} (hF : NumericalComputes F f) :
    SyntaxComputable (fun e => Term.churchNumeral (f e)) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  exact ⟨numericalCompose numeralCodeTerm F,hn.comp hF⟩

private theorem syntax_program : SyntaxComputable Term.programSyntax :=
  ⟨programCodeTerm,programCodeTerm_closed,programCodeTerm_apply⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now put $Z:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$.
    It reverses decision bits. For each $e$, form named representatives of
    $$\begin{aligned}
    S_e&:=\LambdaRelativeSearch{P_e},\qquad s(e):=\LambdaSyntaxCode{S_e},\\
    B_s&:=\lambdaab{z}{\LambdaNumericPair\,
     ((\lambdaab{j}{\ChurchNumeral{s}})z)\,((\lambdaab{j}{j})z)},\\
    Q_e&:=\lambdaab{o}{\lambdaab{n}{Ho(B_{s(e)}n)}},\\
    N_e&:=\lambdaab{o}{\lambdaab{n}{Z(P_eon)}},\\
    \xi(e)&:=\LambdaSyntaxCode{Q_e},\qquad
    \nu(e):=\LambdaSyntaxCode{N_e},\qquad
    \upsilon(e):=\nu(\xi(\nu(e))).
    \end{aligned}$$
    Use fixed named representatives of the closed library terms and expand the search template from
    §{sec:lambda-total-enumerations} before taking its code. These choices are made once, before any
    $e$ or $\varepsilon$ is supplied.
-/
def searchSyntax (S Z B O P : Term) : Term :=
  .lam 70 (.lam 71 (.app (.app S
    (.lam 72 (.app Z (.app (.app P (.var 70)) (.app (.app B (.var 71)) (.var 72)))))) O))

theorem mk_searchSyntax (S Z B O P : Term)
    (hS : mk S = resultSearchTerm) (hZ : mk Z = reverseZeroTerm)
    (hB : mk B = numericalPairTerm) (hO : mk O = numericalConstant 1) :
    mk (searchSyntax S Z B O P) = relativeSearchProgram (mk P) := by
  unfold searchSyntax
  simp only [← lam_mk,← app_mk,hS,hZ,hB,hO]
  rfl

private theorem searchSyntax_computable (S Z B O : Term) :
    SyntaxComputable (fun e => searchSyntax S Z B O (Term.programSyntax e)) := by
  exact syntax_lam (syntax_lam (syntax_app
    (syntax_app (syntax_const S) (syntax_lam (syntax_app (syntax_const Z)
      (syntax_app (syntax_app syntax_program (syntax_const (.var 70)))
        (syntax_app (syntax_app (syntax_const B) (syntax_const (.var 71)))
          (syntax_const (.var 72))))) 72)) (syntax_const O)) 71) 70

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now put $Z:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$.
    It reverses decision bits. For each $e$, form named representatives of
    $$\begin{aligned}
    S_e&:=\LambdaRelativeSearch{P_e},\qquad s(e):=\LambdaSyntaxCode{S_e},\\
    B_s&:=\lambdaab{z}{\LambdaNumericPair\,
     ((\lambdaab{j}{\ChurchNumeral{s}})z)\,((\lambdaab{j}{j})z)},\\
    Q_e&:=\lambdaab{o}{\lambdaab{n}{Ho(B_{s(e)}n)}},\\
    N_e&:=\lambdaab{o}{\lambdaab{n}{Z(P_eon)}},\\
    \xi(e)&:=\LambdaSyntaxCode{Q_e},\qquad
    \nu(e):=\LambdaSyntaxCode{N_e},\qquad
    \upsilon(e):=\nu(\xi(\nu(e))).
    \end{aligned}$$
    Use fixed named representatives of the closed library terms and expand the search template from
    §{sec:lambda-total-enumerations} before taking its code. These choices are made once, before any
    $e$ or $\varepsilon$ is supplied.
-/
def haltingSectionSyntax (H B : Term) (s : ℕ) : Term :=
  .lam 1 (.lam 2 (.app (.app H (.var 1))
    (.app (.lam 40 (.app
      (.app B (.app (.lam 40 (Term.churchNumeral s)) (.var 40)))
      (.app (.lam 40 (.var 40)) (.var 40)))) (.var 2))))

theorem mk_haltingSectionSyntax (H B : Term) (s : ℕ)
    (hH : mk H = haltingDecisionProgram) (hB : mk B = numericalPairTerm) :
    mk (haltingSectionSyntax H B s) =
      reindexProgram haltingDecisionProgram (pairNumerical (numericalConstant s) numericalIdentity) := by
  unfold haltingSectionSyntax
  simp only [← lam_mk,← app_mk,Term.mk_churchNumeral,hH,hB]
  rfl

private theorem haltingSectionSyntax_computable (H B : Term) {f : ℕ → ℕ} {F : AlphaTerm}
    (hF : NumericalComputes F f) : SyntaxComputable (fun e => haltingSectionSyntax H B (f e)) := by
  have hpair := syntax_lam (syntax_app
    (syntax_app (syntax_const B) (syntax_app (syntax_lam (syntax_numeral hF) 40) (syntax_const (.var 40))))
    (syntax_const (.app (.lam 40 (.var 40)) (.var 40)))) 40
  exact syntax_lam (syntax_lam (syntax_app
    (syntax_app (syntax_const H) (syntax_const (.var 1)))
    (syntax_app hpair (syntax_const (.var 2)))) 2) 1

private theorem closedProgram_of_mk_closed (T : Term) {P : AlphaTerm}
    (h : mk T = P) (hc : P.Closed) : Term.closedProgram T.code = P := by
  have ht : T.fv = ∅ := by
    change (mk T).Closed
    rw [h]
    exact hc
  simp only [Term.closedProgram,Term.decode_code,ht,ite_true,h]

/-- The compiler is a total numerical lambda program, uniform in every oracle. -/
theorem existential_jump_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (R : ℕ → ℕ → Prop),
        Decides ε (Term.closedProgram e) (fun z : ℕ => R z.unpair.1 z.unpair.2) →
        Decides (jumpName ε) (Term.closedProgram (f e)) (fun n => ∃ k, R n k) := by
  classical
  obtain ⟨S,hS⟩ := Quotient.exists_rep resultSearchTerm
  obtain ⟨Z,hZ⟩ := Quotient.exists_rep reverseZeroTerm
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨O,hO⟩ := Quotient.exists_rep (numericalConstant 1)
  obtain ⟨H,hH⟩ := Quotient.exists_rep haltingDecisionProgram
  change mk S = resultSearchTerm at hS
  change mk Z = reverseZeroTerm at hZ
  change mk B = numericalPairTerm at hB
  change mk O = numericalConstant 1 at hO
  change mk H = haltingDecisionProgram at hH
  let s := fun e => (searchSyntax S Z B O (Term.programSyntax e)).code
  obtain ⟨C,hC⟩ := searchSyntax_computable S Z B O
  obtain ⟨F,hF⟩ := haltingSectionSyntax_computable H B hC
  refine ⟨F,(fun e => (haltingSectionSyntax H B (s e)).code),hF,?_⟩
  intro e ε R hd
  have hs : Term.closedProgram (s e) = relativeSearchProgram (Term.closedProgram e) := by
    apply closedProgram_of_mk_closed
    · simpa only [Term.mk_programSyntax] using mk_searchSyntax S Z B O (Term.programSyntax e) hS hZ hB hO
    · exact relativeSearchProgram_closed (Term.closedProgram_closed e)
  rw [closedProgram_of_mk_closed _ (mk_haltingSectionSyntax H B (s e) hH hB)
    (reindexProgram_closed (haltingDecisionProgram_decides (fun _ => 0)).1
      ((numericalConstant_computes (s e)).pair numericalIdentity_computes).1)]
  have ht : Computes ε (Term.closedProgram e) (fun z : ℕ => if R z.unpair.1 z.unpair.2 then 1 else 0) :=
    ⟨hd.1,fun z => hd.runs z⟩
  have heq (n : ℕ) : (∃ m, OracleRuns ε (relativeSearchProgram (Term.closedProgram e)) n m) ↔
      ∃ k, R n k := by simp [relativeSearchProgram_runs_iff ht,Nat.unpair_pair]
  have h := (haltingDecisionProgram_decides ε).precompNumerical
    ((numericalConstant_computes (s e)).pair numericalIdentity_computes)
    (g := fun n : ℕ => Nat.pair (s e) n) (by simp)
  simpa only [Nat.unpair_pair,hs,heq,jumpName] using h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now put $Z:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$.
    It reverses decision bits. For each $e$, form named representatives of
    $$\begin{aligned}
    S_e&:=\LambdaRelativeSearch{P_e},\qquad s(e):=\LambdaSyntaxCode{S_e},\\
    B_s&:=\lambdaab{z}{\LambdaNumericPair\,
     ((\lambdaab{j}{\ChurchNumeral{s}})z)\,((\lambdaab{j}{j})z)},\\
    Q_e&:=\lambdaab{o}{\lambdaab{n}{Ho(B_{s(e)}n)}},\\
    N_e&:=\lambdaab{o}{\lambdaab{n}{Z(P_eon)}},\\
    \xi(e)&:=\LambdaSyntaxCode{Q_e},\qquad
    \nu(e):=\LambdaSyntaxCode{N_e},\qquad
    \upsilon(e):=\nu(\xi(\nu(e))).
    \end{aligned}$$
    Use fixed named representatives of the closed library terms and expand the search template from
    §{sec:lambda-total-enumerations} before taking its code. These choices are made once, before any
    $e$ or $\varepsilon$ is supplied.
-/
def negateSyntax (Z P : Term) : Term :=
  .lam 1 (.lam 2 (.app Z (.app (.app P (.var 1)) (.var 2))))

theorem mk_negateSyntax (Z P : Term) (hZ : mk Z = reverseZeroTerm) :
    mk (negateSyntax Z P) = mapOutputProgram reverseZeroTerm (mk P) := by
  unfold negateSyntax
  simp only [← lam_mk,← app_mk,hZ]
  rfl

private theorem negateSyntax_computable (Z : Term) :
    SyntaxComputable (fun e => negateSyntax Z (Term.programSyntax e)) := by
  exact syntax_lam (syntax_lam (syntax_app (syntax_const Z)
    (syntax_app (syntax_app syntax_program (syntax_const (.var 1))) (syntax_const (.var 2)))) 2) 1

theorem negation_index_transform :
    ∃ (N : AlphaTerm) (ν : ℕ → ℕ), NumericalComputes N ν ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (R : ℕ → Prop), Decides ε (Term.closedProgram e) R →
        Decides ε (Term.closedProgram (ν e)) (fun n => ¬ R n) := by
  obtain ⟨Z,hZ⟩ := Quotient.exists_rep reverseZeroTerm
  change mk Z = reverseZeroTerm at hZ
  obtain ⟨N,hN⟩ := negateSyntax_computable Z
  refine ⟨N,(fun e => (negateSyntax Z (Term.programSyntax e)).code),hN,?_⟩
  intro e ε R hd
  have hm := mk_negateSyntax Z (Term.programSyntax e) hZ
  rw [Term.mk_programSyntax] at hm
  rw [closedProgram_of_mk_closed _ hm (mapOutputProgram_closed reverseZero_computes.1 hd.1)]
  exact hd.negate

theorem universal_jump_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (R : ℕ → ℕ → Prop),
        Decides ε (Term.closedProgram e) (fun z : ℕ => R z.unpair.1 z.unpair.2) →
        Decides (jumpName ε) (Term.closedProgram (f e)) (fun n => ∀ k, R n k) := by
  obtain ⟨X,ξ,hX,hx⟩ := existential_jump_index_transform
  obtain ⟨N,ν,hN,hn⟩ := negation_index_transform
  refine ⟨numericalCompose N (numericalCompose X N),(fun e => ν (ξ (ν e))),hN.comp (hX.comp hN),?_⟩
  intro e ε R hd
  have h := hn (ξ (ν e)) (jumpName ε) (fun n => ∃ k, ¬ R n k)
    (hx (ν e) ε (fun n k => ¬ R n k) (hn e ε _ hd))
  simpa only [not_exists,not_not] using h

theorem forall_exists_jump_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (R : ℕ → ℕ → ℕ → Prop),
        Decides ε (Term.closedProgram e)
          (fun z : ℕ => R z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2) →
        Decides (jumpName (jumpName ε)) (Term.closedProgram (f e)) (fun n => ∀ t, ∃ b, R n t b) := by
  obtain ⟨X,ξ,hX,hx⟩ := existential_jump_index_transform
  obtain ⟨U,υ,hU,hu⟩ := universal_jump_index_transform
  refine ⟨numericalCompose U X,(fun e => υ (ξ e)),hU.comp hX,?_⟩
  intro e ε R hd
  exact hu (ξ e) (jumpName ε) (fun n t => ∃ b, R n t b)
    (hx e ε (fun z b => R z.unpair.1 z.unpair.2 b) hd)

/-- One simultaneous choice of the three compilers, before every oracle and predicate. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Numerical quantifiers from jumps
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Lambda index transformations for quantifiers
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First reduce arbitrary numerical halting to diagonal halting. Insert $\ChurchNumeral{n}$ into the closed
    program $\lambdaab{o}{\lambdaab{t}{P_eo\ChurchNumeral{n}}}$, and let $h(e,n)$ be its syntax index.
    The code constructors compute $h$, independently of $\varepsilon$. Two beta steps discard $t$;
    confluence gives the reverse implication for every numeral output. Hence
    $$h(e,n)\in K^\varepsilon\quad\Longleftrightarrow\quad
      \exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{n}}{\ChurchNumeral{m}}.$$
    A query to $\varepsilon'$ therefore decides this halting question.

    Next construct a program that searches $k=0,1,\ldots$ for an accepting computation of $P_e$ on
    $\NatPair{n}{k}$. Since $P_e$ is a decider, every trial terminates. Exact search returns one when a
    witness exists and has no numerical output otherwise. Apply the halting query to this search program.
    The search template and its halting-query wrapper have syntax codes computable from $e$; this gives
    $\xi$. Reversing a decision bit gives $\nu$. Applying this reversal before and after the existential
    construction gives $\upsilon$, since $\forall k\,R(n,k)$ is equivalent to $\neg\exists k\,\neg R(n,k)$.
    Apply the existential and universal constructions successively for the last assertion.
    §{sec:lambda-relative-jump} gives the closed templates and their code transformations.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The search template consists of fixed closed terms, applications, abstractions, and the inserted
    representative of $P_e$. Hence the code constructors compute $s(e)$. The numeral-code term then supplies
    $\LambdaSyntaxCode{\ChurchNumeral{s(e)}}$, and the same constructors compute $\xi(e)$. They also compute
    $\nu(e)$ directly from the template $N_e$. Composition gives $\upsilon$.
    All resulting syntax is closed, so decoding these indices gives the displayed programs.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Suppose $P_e$ decides $R$. Every trial of $S_e$ terminates; the exact-search theorem says that $S_e$ on
    input $n$ returns one precisely when some $k$ satisfies $R(n,k)$, and has no numerical output otherwise.
    The halting reduction shows that $Q_e$ with parameter $\varepsilon'$ returns the characteristic bit
    of this existential statement. The term $N_e$ reverses zero and one, proving the negation assertion.
    Negate the original predicate, apply the existential construction, and negate the answer to obtain
    the universal assertion. These finite code constructions precede every use of the input parameter.
    Applying $\xi$ to a decider on $\NatPair{\NatPair{n}{t}}{b}$ and then $\upsilon$ gives a decider for
    $\forall t\,\exists b\,R(n,t,b)$ at $(\varepsilon')'$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now put $Z:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$.
    It reverses decision bits. For each $e$, form named representatives of
    $$\begin{aligned}
    S_e&:=\LambdaRelativeSearch{P_e},\qquad s(e):=\LambdaSyntaxCode{S_e},\\
    B_s&:=\lambdaab{z}{\LambdaNumericPair\,
     ((\lambdaab{j}{\ChurchNumeral{s}})z)\,((\lambdaab{j}{j})z)},\\
    Q_e&:=\lambdaab{o}{\lambdaab{n}{Ho(B_{s(e)}n)}},\\
    N_e&:=\lambdaab{o}{\lambdaab{n}{Z(P_eon)}},\\
    \xi(e)&:=\LambdaSyntaxCode{Q_e},\qquad
    \nu(e):=\LambdaSyntaxCode{N_e},\qquad
    \upsilon(e):=\nu(\xi(\nu(e))).
    \end{aligned}$$
    Use fixed named representatives of the closed library terms and expand the search template from
    §{sec:lambda-total-enumerations} before taking its code. These choices are made once, before any
    $e$ or $\varepsilon$ is supplied.
-/
theorem quantifier_index_transforms :
    ∃ (X N U : AlphaTerm) (ξ ν υ : ℕ → ℕ),
      NumericalComputes X ξ ∧ NumericalComputes N ν ∧ NumericalComputes U υ ∧
      (∀ e, υ e = ν (ξ (ν e))) ∧ ∀ ε : ℕ → ℕ,
      (∀ (e : ℕ) (R : ℕ → ℕ → Prop),
        Decides ε (Term.closedProgram e) (fun z : ℕ => R z.unpair.1 z.unpair.2) →
        Decides (jumpName ε) (Term.closedProgram (ξ e)) (fun n => ∃ k, R n k)) ∧
      (∀ (e : ℕ) (S : ℕ → Prop), Decides ε (Term.closedProgram e) S →
        Decides ε (Term.closedProgram (ν e)) (fun n => ¬ S n)) ∧
      (∀ (e : ℕ) (R : ℕ → ℕ → Prop),
        Decides ε (Term.closedProgram e) (fun z : ℕ => R z.unpair.1 z.unpair.2) →
        Decides (jumpName ε) (Term.closedProgram (υ e)) (fun n => ∀ k, R n k)) ∧
      (∀ (e : ℕ) (R : ℕ → ℕ → ℕ → Prop),
        Decides ε (Term.closedProgram e)
          (fun z : ℕ => R z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2) →
        Decides (jumpName (jumpName ε)) (Term.closedProgram (υ (ξ e)))
          (fun n => ∀ t, ∃ b, R n t b)) := by
  obtain ⟨X,ξ,hX,hx⟩ := existential_jump_index_transform
  obtain ⟨N,ν,hN,hn⟩ := negation_index_transform
  let υ := fun e => ν (ξ (ν e))
  have hu (e : ℕ) (ε : ℕ → ℕ) (R : ℕ → ℕ → Prop)
      (hd : Decides ε (Term.closedProgram e) (fun z : ℕ => R z.unpair.1 z.unpair.2)) :
      Decides (jumpName ε) (Term.closedProgram (υ e)) (fun n => ∀ k, R n k) := by
    have h := hn (ξ (ν e)) (jumpName ε) (fun n => ∃ k, ¬ R n k)
      (hx (ν e) ε (fun n k => ¬ R n k) (hn e ε _ hd))
    simpa only [not_exists,not_not] using h
  refine ⟨X,N,numericalCompose N (numericalCompose X N),ξ,ν,υ,hX,hN,
    hN.comp (hX.comp hN),fun _ => rfl,fun ε => ?_⟩
  refine ⟨fun e R => hx e ε R,fun e S => hn e ε S,fun e R => hu e ε R,?_⟩
  intro e R hd
  exact hu (ξ e) (jumpName ε) (fun n t => ∃ b, R n t b)
    (hx e ε (fun z b => R z.unpair.1 z.unpair.2 b) hd)

end LambdaRelative
end PolishSpaceBook
