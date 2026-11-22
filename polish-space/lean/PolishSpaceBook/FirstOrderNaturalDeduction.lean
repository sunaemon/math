module

public import PolishSpaceBook.FirstOrderDeductionSemantics

@[expose] public section

/-!
# The logic appendix's natural-deduction calculus

Contexts are finite sets of alpha-classes. Constructors are exactly the printed
primitive rules, including the existential eigenvariable side condition and
equality elimination by capture-avoiding substitution. Soundness is proved by
induction on derivations.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{}{\Gamma, \varphi \vdash \varphi}\,(\text{Ax})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma \vdash \varphi \quad \Gamma \vdash \psi}{\Gamma \vdash \varphi \land \psi}\,(\land\text{I}) \qquad
    \dfrac{\Gamma \vdash \varphi \land \psi}{\Gamma \vdash \varphi}\,(\land\text{E}_1) \qquad
    \dfrac{\Gamma \vdash \varphi \land \psi}{\Gamma \vdash \psi}\,(\land\text{E}_2)$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma \vdash \varphi}{\Gamma \vdash \varphi \lor \psi}\,(\lor\text{I}_1) \qquad
    \dfrac{\Gamma \vdash \psi}{\Gamma \vdash \varphi \lor \psi}\,(\lor\text{I}_2) \qquad
    \dfrac{\Gamma \vdash \varphi \lor \psi \quad \Gamma, \varphi \vdash \chi \quad \Gamma, \psi \vdash \chi}{\Gamma \vdash
    \chi}\,(\lor\text{E})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma, \varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}\,(\to\text{I}) \qquad
    \dfrac{\Gamma \vdash \varphi \to \psi \quad \Gamma \vdash \varphi}{\Gamma \vdash \psi}\,(\to\text{E})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma \vdash \bot}{\Gamma \vdash \chi}\,(\bot\text{E})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma \vdash \varphi(x)}{\Gamma \vdash \forall x\, \varphi(x)}\,(\forall\text{I},\ \text{where } x \notin
    \FreeVars{\Gamma}) \qquad
    \dfrac{\Gamma \vdash \forall x\, \varphi(x)}{\Gamma \vdash \varphi(t)}\,(\forall\text{E})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma \vdash \varphi(t)}{\Gamma \vdash \exists x\, \varphi(x)}\,(\exists\text{I})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{\Gamma \vdash \exists x\, \varphi(x) \quad \Gamma, \varphi(y) \vdash \chi}{\Gamma \vdash
    \chi}\,(\exists\text{E})$$
    The side condition on existential elimination is
    $$y \notin \FreeVars{\Gamma} \cup \FreeVars{\chi} \cup \FreeVars{\existsbind{x}{\varphi}}.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{}{\Gamma \vdash t = t}\,(=\text{I}) \qquad
    \dfrac{\Gamma \vdash \varphi(t_0) \quad \Gamma \vdash t_0 = t_1}{\Gamma \vdash \varphi(t_1)}\,(=\text{E})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\dfrac{}{\Gamma \vdash \varphi \lor \neg \varphi}\,(\text{LEM})$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The rule $(\to\text{E})$ is \termdefine{modus ponens}, $(\bot\text{E})$ is \termdefine{ex falso quodlibet}, and (LEM) is
    the \termdefine{law of excluded middle}.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Deduction.** The formal derivability relation is the syntactic side of the later comparison with classical semantic
    truth. A \termdefine{sequent} in a language $L$ is a pair $\Gamma \vdash \varphi$ in which the
    \termdefineas{hypothesis}{hypotheses} $\Gamma$ form a finite set of $L$-formulas and the \termdefine{conclusion}
    $\varphi$ is an $L$-formula. We write $\Gamma,\varphi$ for $\Gamma \cup \{\varphi\}$. Thus an assumption may be used
    repeatedly inside a proof; this is contraction, built into the finite-set convention. Each \termdefine{inference rule}
    below — one or two rules per connective, plus an axiom (Ax) for assumption, equality rules ($=$I, $=$E), and classically
    the law of excluded middle (LEM) — is a syntactic relation between a finite list of premise sequents and a conclusion
    sequent: given a candidate $(S_1, \ldots, S_n; S)$, one checks whether the tuple matches the rule schema and satisfies
    its side condition. \termdefineas{introduction rule}{Introduction} rules (I) build a connective into the conclusion;
    \termdefineas{elimination rule}{elimination} rules (E) decompose a connective in a hypothesis or premise. A
    \termdefine{proof} is a finite rooted tree whose nodes are labeled by sequents such that, at each non-leaf node $S$, the
    labels of its children are the premises of some rule instance with conclusion $S$, and each leaf is the conclusion of a
    nullary rule.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Since hypotheses are
    finite sets, exchange and contraction are built in. A sequent $\Gamma \vdash\varphi$ is
    \termdefine{derivable} iff some proof has it as root. The renaming and weakening lemma below justifies enlarging
    the hypothesis set, including the necessary changes of eigenvariables.
-/
inductive Derives : Context L → AlphaFormula L → Prop where
  | hyp (Γ : Context L) (φ : AlphaFormula L) : Derives (insert φ Γ) φ
  | andIntro {Γ : Context L} {φ ψ : AlphaFormula L} :
      Derives Γ φ → Derives Γ ψ → Derives Γ (binary .conj φ ψ)
  | andLeft {Γ : Context L} {φ ψ : AlphaFormula L} :
      Derives Γ (binary .conj φ ψ) → Derives Γ φ
  | andRight {Γ : Context L} {φ ψ : AlphaFormula L} :
      Derives Γ (binary .conj φ ψ) → Derives Γ ψ
  | orLeft {Γ : Context L} {φ : AlphaFormula L} (ψ : AlphaFormula L) :
      Derives Γ φ → Derives Γ (binary .disj φ ψ)
  | orRight {Γ : Context L} (φ : AlphaFormula L) {ψ : AlphaFormula L} :
      Derives Γ ψ → Derives Γ (binary .disj φ ψ)
  | orElim {Γ : Context L} {φ ψ χ : AlphaFormula L} :
      Derives Γ (binary .disj φ ψ) →
      Derives (insert φ Γ) χ → Derives (insert ψ Γ) χ → Derives Γ χ
  | impIntro {Γ : Context L} {φ ψ : AlphaFormula L} :
      Derives (insert φ Γ) ψ → Derives Γ (binary .imp φ ψ)
  | impElim {Γ : Context L} {φ ψ : AlphaFormula L} :
      Derives Γ (binary .imp φ ψ) → Derives Γ φ → Derives Γ ψ
  | falseElim {Γ : Context L} (φ : AlphaFormula L) :
      Derives Γ falsum → Derives Γ φ
  | allIntro {Γ : Context L} {φ : AlphaFormula L} (x : ℕ) :
      Derives Γ φ → x ∉ Γ.fv → Derives Γ (quant .all x φ)
  | allElim {Γ : Context L} (x : ℕ) (φ : AlphaFormula L) (t : L.Term ℕ) :
      Derives Γ (quant .all x φ) → Derives Γ (φ.subst x t)
  | exIntro {Γ : Context L} (x : ℕ) (φ : AlphaFormula L) (t : L.Term ℕ) :
      Derives Γ (φ.subst x t) → Derives Γ (quant .ex x φ)
  | exElim {Γ : Context L} (x y : ℕ) (φ χ : AlphaFormula L) :
      Derives Γ (quant .ex x φ) → Derives (insert (φ.subst x (.var y)) Γ) χ →
      y ∉ Γ.fv ∪ χ.fv ∪ (quant .ex x φ).fv → Derives Γ χ
  | eqIntro (Γ : Context L) (t : L.Term ℕ) : Derives Γ (equal t t)
  | eqElim {Γ : Context L} (φ : AlphaFormula L) (x : ℕ) (t r : L.Term ℕ) :
      Derives Γ (φ.subst x t) → Derives Γ (equal t r) → Derives Γ (φ.subst x r)
  | excludedMiddle (Γ : Context L) (φ : AlphaFormula L) :
      Derives Γ (binary .disj φ (neg φ))

namespace Derives

theorem assumption {Γ : Context L} {φ : AlphaFormula L} (hφ : φ ∈ Γ) : Derives Γ φ := by
  simpa only [Finset.insert_eq_of_mem hφ] using Derives.hyp Γ φ

/-- Negation introduction is implication introduction with falsity as conclusion. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Derived rules.** A rule is \termdefine{derived} if every instance can be obtained by a fixed combination of primitive
    rules. Since $\neg\varphi$ abbreviates $\varphi\to\bot$, the usual negation rules are derived:
    $$\dfrac{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg \varphi}\,(\neg\text{I}) \qquad
    \dfrac{\Gamma \vdash \varphi \quad \Gamma \vdash \neg \varphi}{\Gamma \vdash \chi}\,(\neg\text{E}).$$
    $(\neg\text{I})$ is $(\to\text{I})$ with $\psi := \bot$. For $(\neg\text{E})$, expand $\neg\varphi$ to $\varphi\to\bot$,
    apply $(\to\text{E})$ to obtain $\Gamma \vdash \bot$, then $(\bot\text{E})$ delivers $\Gamma \vdash \chi$.
-/
theorem negIntro {Γ : Context L} {φ : AlphaFormula L}
    (h : Derives (insert φ Γ) falsum) : Derives Γ (neg φ) :=
  .impIntro h

/-- Negation elimination uses implication elimination followed by falsity elimination. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Derived rules.** A rule is \termdefine{derived} if every instance can be obtained by a fixed combination of primitive
    rules. Since $\neg\varphi$ abbreviates $\varphi\to\bot$, the usual negation rules are derived:
    $$\dfrac{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg \varphi}\,(\neg\text{I}) \qquad
    \dfrac{\Gamma \vdash \varphi \quad \Gamma \vdash \neg \varphi}{\Gamma \vdash \chi}\,(\neg\text{E}).$$
    $(\neg\text{I})$ is $(\to\text{I})$ with $\psi := \bot$. For $(\neg\text{E})$, expand $\neg\varphi$ to $\varphi\to\bot$,
    apply $(\to\text{E})$ to obtain $\Gamma \vdash \bot$, then $(\bot\text{E})$ delivers $\Gamma \vdash \chi$.
-/
theorem negElim {Γ : Context L} {φ : AlphaFormula L} (χ : AlphaFormula L)
    (hφ : Derives Γ φ) (hn : Derives Γ (neg φ)) : Derives Γ χ :=
  .falseElim χ (.impElim hn hφ)

/-- Every displayed primitive rule preserves truth under every assignment. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Soundness
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Induct on the derivation. The assumption rule uses a formula already satisfied by the assignment.
    The conjunction and disjunction introduction rules and conjunction elimination follow directly from the semantic
    clauses. For disjunction elimination, one disjunct is true, so the induction hypothesis for its branch applies to
    the context enlarged by that disjunct. For implication introduction, assume the antecedent is true and apply
    induction to the enlarged context; implication elimination then uses the resulting implication.
    Falsity elimination has an impossible true premise, and excluded middle is valid in classical semantics.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For $(\forall\text{I})$, the side condition $x\notin\FreeVars{\Gamma}$ and assignment locality show that
    $s[x\mapsto a]$ satisfies $\Gamma$ for every $a\in M$. The induction hypothesis therefore gives
    $\mathcal M,s[x\mapsto a]\models\varphi$ for every such $a$, which is the universal clause.
    For $(\forall\text{E})$, evaluate the universal premise at $t^{\mathcal M,s}$ and use the substitution lemma.
    For $(\exists\text{I})$, the same lemma shows that $t^{\mathcal M,s}$ is a witness.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For $(\exists\text{E})$, choose $a\in M$ with $\mathcal M,s[x\mapsto a]\models\varphi$.
    The side condition gives
    $$y\notin\FreeVars{\Gamma}\cup\FreeVars{\chi}\cup\FreeVars{\existsbind{x}{\varphi}}.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Put $s'=s[y\mapsto a]$. This assignment still satisfies $\Gamma$. Moreover, the substitution lemma gives
    $$\mathcal M,s'\models\varphi\subst{x}{y}
    \quad\Longleftrightarrow\quad
    \mathcal M,s[y\mapsto a][x\mapsto a]\models\varphi.$$
    The assignments on the right and $s[x\mapsto a]$ agree on $\FreeVars{\varphi}$:
    both assign $a$ to $x$, and a free variable of the body different from $x$ cannot be $y$ by the side condition.
    This also covers $y=x$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Assignment locality therefore makes the extra premise true under $s'$.
    Apply induction to the second derivation to obtain $\mathcal M,s'\models\chi$.
    Since $y\notin\FreeVars{\chi}$, assignment locality gives $\mathcal M,s\models\chi$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Equality introduction is reflexivity in the domain. For equality elimination, the equality premise gives
    $t_0^{\mathcal M,s}=t_1^{\mathcal M,s}$. By the substitution lemma, the instances
    $\varphi\subst{x}{t_0}$ and $\varphi\subst{x}{t_1}$ are evaluated under the same updated assignment,
    so the truth of the first implies the truth of the second.
-/
theorem sound {Γ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ)
    (s : ℕ → M) (hΓ : Γ.Realize s) : φ.Realize s := by
  induction h generalizing s with
  | hyp Γ φ => exact hΓ φ (Finset.mem_insert_self _ _)
  | andIntro hφ hψ ihφ ihψ =>
    exact (realize_conj _ _ s).mpr ⟨ihφ s hΓ, ihψ s hΓ⟩
  | andLeft h ih => exact ((realize_conj _ _ s).mp (ih s hΓ)).1
  | andRight h ih => exact ((realize_conj _ _ s).mp (ih s hΓ)).2
  | orLeft ψ h ih => exact (realize_disj _ _ s).mpr (Or.inl (ih s hΓ))
  | orRight φ h ih => exact (realize_disj _ _ s).mpr (Or.inr (ih s hΓ))
  | orElim hdisj hφ hψ ihdisj ihφ ihψ =>
    rcases (realize_disj _ _ s).mp (ihdisj s hΓ) with hφ | hψ
    · exact ihφ s ((Context.realize_insert _ _ s).mpr ⟨hφ, hΓ⟩)
    · exact ihψ s ((Context.realize_insert _ _ s).mpr ⟨hψ, hΓ⟩)
  | impIntro h ih =>
    apply (realize_imp _ _ s).mpr
    intro hφ
    exact ih s ((Context.realize_insert _ _ s).mpr ⟨hφ, hΓ⟩)
  | impElim hf ha ihf iha => exact (realize_imp _ _ s).mp (ihf s hΓ) (iha s hΓ)
  | falseElim φ h ih => exact (realize_falsum s (ih s hΓ)).elim
  | allIntro x h hx ih =>
    apply (realize_all _ _ s).mpr
    intro a
    exact ih (Function.update s x a) ((Context.realize_update _ s x a hx).mpr hΓ)
  | allElim x φ t h ih =>
    apply (realize_subst φ x t s).mpr
    exact (realize_all _ _ s).mp (ih s hΓ) (t.realize s)
  | exIntro x φ t h ih =>
    apply (realize_ex _ _ s).mpr
    exact ⟨t.realize s, (realize_subst φ x t s).mp (ih s hΓ)⟩
  | @exElim Γ x y φ χ hex hcase hy ihex ihcase =>
    have hf : y ∉ Γ.fv ∧ y ∉ χ.fv ∧ y ∉ (quant .ex x φ).fv := by
      simpa only [Finset.mem_union, not_or, and_assoc] using hy
    obtain ⟨a, ha⟩ := (realize_ex _ _ s).mp (ihex s hΓ)
    have hΓ' : Γ.Realize (Function.update s y a) :=
      (Context.realize_update Γ s y a hf.1).mpr hΓ
    have hφ' : (φ.subst x (.var y)).Realize (Function.update s y a) :=
      (realize_eigeninstance φ x y s a hf.2.2).mpr ha
    have hχ := ihcase (Function.update s y a)
      ((Context.realize_insert _ _ _).mpr ⟨hφ', hΓ'⟩)
    exact (χ.realize_update s y a hf.2.1).mp hχ
  | eqIntro Γ t => exact (realize_equal _ _ s).mpr rfl
  | eqElim φ x t r hsub heq ihsub iheq =>
    have he := (realize_equal _ _ s).mp (iheq s hΓ)
    apply (realize_subst φ x r s).mpr
    have ht := (realize_subst φ x t s).mp (ihsub s hΓ)
    rwa [he] at ht
  | excludedMiddle Γ φ =>
    classical
    apply (realize_disj _ _ s).mpr
    rcases Classical.em (φ.Realize s) with hp | hn
    · exact Or.inl hp
    · exact Or.inr ((realize_neg φ s).mpr hn)

end Derives

/-- Derivability from an arbitrary set of axioms uses a finite context. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{theory} in a language $L$ is a set $T$ of $L$-sentences, called its \termdefineas{axiom}{axioms}; the
    notation $T\vdash\varphi$ means that $\Gamma\vdash\varphi$ for some finite $\Gamma\IncludedIn T$. The
    consequences of $T$ are the sentences in its \termdefine{deductive closure} $\{\varphi : T \vdash \varphi\}$. When an
    axiom schema is written using an open formula, each instance is its universal closure: all free variables not explicitly
    bound in the displayed formula are universally quantified outside the displayed expression. In schemas with parameters,
    such as Replacement and Separation, the parameters are precisely those additional free variables before this universal
    closure is applied. \termdefine{ZFC} is the $L_\in$-theory whose axioms are listed in §{sec:zfc-axioms}.
-/
def ProvesFrom (T : Set (AlphaFormula L)) (φ : AlphaFormula L) : Prop :=
  ∃ Γ : Context L, (∀ ψ ∈ Γ, ψ ∈ T) ∧ Derives Γ φ

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The forward implication is the \termuse{first-order soundness theorem}, since a derivation from $T$ uses only
    finitely many axioms.
-/
theorem ProvesFrom.sound {T : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (h : ProvesFrom T φ) (s : ℕ → M) (hT : ∀ ψ ∈ T, ψ.Realize s) : φ.Realize s := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  exact hd.sound s (fun ψ hψ => hT ψ (hΓ ψ hψ))

/-- A model on a nonempty domain rules out a derivation of falsity. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: corollary
  title: Models imply consistency
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Choose an assignment in the model's nonempty domain. If $T\vdash\bot$, some finite set of axioms of $T$
    derives $\bot$. The assignment satisfies those axioms, so the \termuse{first-order soundness theorem} would make
    $\bot$ true, a contradiction.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $\varphi$ is a sentence, its truth does not depend on $s$, and we write $\mathcal M \models \varphi$. A model
    $\mathcal M$ satisfies a theory $T$, written $\mathcal M \models T$, if $\mathcal M \models \sigma$ for every sentence
    $\sigma \in T$.
-/
theorem not_proves_falsum_of_model [Nonempty M] {T : Set (AlphaFormula L)}
    (hT : ∀ (s : ℕ → M) ψ, ψ ∈ T → ψ.Realize s) : ¬ProvesFrom T falsum := by
  intro h
  let s : ℕ → M := fun _ => Classical.choice ‹Nonempty M›
  exact realize_falsum s (h.sound s (hT s))

end PolishSpaceBook.NamedFirstOrder
