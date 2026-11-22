module

public import PolishSpaceBook.LambdaAssemblies
public import PolishSpaceBook.LambdaNumericalSearch

@[expose] public section

/-! # The halting obstruction to uniform excluded middle

Every program here is a closed lambda term. Halting means returning a Church
numeral on the program's own numerical index. The final obstruction uses strict
predicates on the natural-number assembly, whose input extent supplies the index.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-- Numerical halting on the program's own index. -/
def diagonalHalts (e : ℕ) : Prop := ∃ m, App e e m

noncomputable local instance (e : ℕ) : Decidable (diagonalHalts e) := Classical.propDecidable _

/-- A program returning zero exactly on the halting set cannot exist. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: Undecidability of diagonal halting
  excerpt: |
    \begin{lemma*}[\termdefineas{undecidability of diagonal halting}{Undecidability of diagonal halting}]
    Put $K:=\{e\in\NN:\varphi_e(e)\text{ is defined}\}$, where defined means that evaluation returns a Church numeral.
    There is no closed lambda program computing the total function that returns $0$ on $K$ and $1$ outside $K$.
    \end{lemma*}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Suppose that a closed program $D$ computes this function. Use the first numerical projection to form
    $$T:=\lambdaab{z}{D(\LambdaNumericProjection{1}\,z)}.$$
    On input $\NatPair{e}{k}$, this total test returns $0$ if $e\in K$ and $1$ otherwise, independently of $k$.
    Apply the parameterized numerical search of §{sec:lambda-rational-ball-programs} to $T$.
    The resulting closed term $S_T$ searches for the least $k$ with a nonzero test answer, and consequently
    $$S_T\ChurchNumeral{e}\text{ has a numeral output}\quad\Longleftrightarrow\quad e\notin K.$$
    Choose an index $d$ of $S_T$ in the fixed enumeration of closed programs. On input $d$, the definition of $K$ gives
    $$d\in K\quad\Longleftrightarrow\quad
      S_T\ChurchNumeral{d}\text{ has a numeral output}\quad\Longleftrightarrow\quad d\notin K,$$
    a contradiction. Both the search and the evaluation use ordinary beta reduction.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    If $K$ were decidable, define a partial computable function
    $$
    d(e)=
    \begin{cases}
    \uparrow, & \varphi_e(e)\downarrow,\\
    0, & \varphi_e(e)\uparrow.
    \end{cases}
    $$
    Let $d=\varphi_m$ for some index $m$. Then
    $$
    \varphi_m(m)\downarrow
    \quad\Longleftrightarrow\quad
    d(m)\downarrow
    \quad\Longleftrightarrow\quad
    \varphi_m(m)\uparrow,
    $$
    a contradiction. Hence $K$ is not decidable.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Fix an effective enumeration $(\varphi_e)$ of the partial numerical functions computed by closed lambda terms, and let
    $$K:=\{e\in\NN:\varphi_e(e)\downarrow\}.$$
    Here the downward arrow means that the computation returns a numeral. The set $K$ is recursively enumerable by finite
    simulation, but undecidable. Indeed, a decider would give a program that returns zero on $e\notin K$ and diverges on
    $e\in K$; applying that program to its own index gives a contradiction.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Undecidability of halting.** The \termdefine{halting problem} concerns the set
        $$
        K=\{e:\varphi_e(e)\downarrow\}
        $$
        which is recursively enumerable but not decidable.
-/
theorem diagonalHalts_not_decidable :
    ¬ ∃ D : AlphaTerm, NumericalComputes D (fun e => if diagonalHalts e then 0 else 1) := by
  classical
  rintro ⟨D,hD⟩
  have ht := hD.comp (projection_computes true)
  obtain ⟨d,hd⟩ := Term.closedProgram_surjective _ (numericalSearch_closed ht.1)
  have heq : diagonalHalts d ↔ ¬ diagonalHalts d := by
    change (∃ m, Relation.ReflTransGen Beta
      (app (Term.closedProgram d) (numeral d)) (numeral m)) ↔ _
    rw [hd, numericalSearch_domain ht]
    change (∃ k, (if diagonalHalts (Nat.pair d k).unpair.1 then 0 else 1) ≠ 0) ↔ _
    simp only [Nat.unpair_pair]
    by_cases h : diagonalHalts d <;> simp [h]
  have hn : ¬ diagonalHalts d := fun h => (heq.mp h) h
  exact hn (heq.mpr hn)

/-- Natural numbers carry their own indices as realizers. -/
def naturalAssembly : Assembly where
  Carrier := ℕ
  realizes e := {e}
  inhabited e := ⟨e,rfl⟩

/-- Retain the input extent alongside a numerical halting output. -/
def haltingPredicate (e : ℕ) : Set ℕ :=
  {z | z.unpair.1 = e ∧ App e e z.unpair.2}

theorem haltingPredicate_nonempty (e : ℕ) :
    (haltingPredicate e).Nonempty ↔ diagonalHalts e := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.unpair.2,hz.2⟩
  · rintro ⟨m,hm⟩
    exact ⟨Nat.pair e m,by simp [haltingPredicate,hm]⟩

/-- This predicate defines a subobject of the natural-number PER. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    We now retain the input extent explicitly. Let $N$ be the natural-number assembly with $E_N(e)=\{e\}$, and put
    $$H(e):=\{\NatPair{e}{m}:\varphi_e(e)=m\}.$$
    Then $H(e)$ is nonempty exactly when $e\in K$. The first projection uniformly gives $H(e)\le E_N(e)$.
    An equality realizer in $N$ forces equality of the represented natural numbers, so the second projection gives
    $$(e\sim_N e')\land H(e)\le H(e').$$
    Thus $H$ is a strict extensional predicate and defines a subobject of $N$ by
    §{sec:effective-topos-subobjects-truth-values}. This predicate keeps the index available as part of its realizer.
-/
def haltingStrictPredicate : RealizerPER.StrictPredicate naturalAssembly.toPER where
  val := haltingPredicate
  strict := by
    have he : naturalAssembly.toPER.extent = naturalAssembly.realizes :=
      funext (Assembly.extent_toPER naturalAssembly)
    rw [he]
    apply reduces_trans (ψ := realizabilityAnd naturalAssembly.realizes (fun e => {m | App e e m}))
    · exact reduces_of_subset fun e z hz => ⟨hz.1,hz.2⟩
    · exact reduces_and_left _ _
  extensional := by
    let R := fun p : ℕ × ℕ => naturalAssembly.toPER.rel p.1 p.2
    apply reduces_trans (ψ := realizabilityAnd R (fun p => haltingPredicate p.2))
    · apply reduces_of_subset
      intro p z hz
      refine ⟨hz.1,?_⟩
      change z.unpair.2 ∈ haltingPredicate p.2
      rw [← hz.1.1]
      exact hz.2
    · exact reduces_and_right _ _

/-- Reading the disjunction tag would decide halting, for any proposed complement. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: proposition
  title: The halting predicate has no complement
  excerpt: |
    \begin{proposition*}[\termdefineas{halting predicate has no complement}{The halting predicate has no complement}]
    There is no family $Q(e)\IncludedIn\NN$ for which both reductions
    $$E_N\le H\lor Q,\qquad H\land Q\le\bot$$
    hold uniformly in $e$.
    \end{proposition*}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $r$ track the first reduction and $s$ the second. Since $e\in E_N(e)$, the computation $r\cdot e$ always returns
    an element of $H(e)\lor Q(e)$. Write $U:=\LambdaOutputSearch$ and form the closed program
    $$D:=\lambdaab{z}{\LambdaNumericProjection{1}\bigl((U\ChurchNumeral{r})z\bigr)}.$$
    If $r\cdot e=\NatPair{0}{a}$ with $a\in H(e)$, then $e\in K$, and $D$ returns $0$.
    If $r\cdot e=\NatPair{1}{b}$ with $b\in Q(e)$, then $e\notin K$: otherwise there would be an $a\in H(e)$,
    and $s\cdot\NatPair{a}{b}$ would have to belong to the empty truth value $\bot$.
    In this second case $D$ returns $1$. Universal evaluation followed by numerical projection therefore makes $D$
    a total decider of the function excluded by the preceding lemma. This contradiction proves the proposition.
    \end{proof}
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
theorem halting_no_complement (Q : ℕ → Set ℕ)
    (hcover : Reduces naturalAssembly.realizes (realizabilityOr haltingPredicate Q))
    (hdisjoint : Reduces (realizabilityAnd haltingPredicate Q) (realizabilityBot ℕ)) : False := by
  classical
  obtain ⟨r,hr⟩ := (reduces_iff _ _).mp hcover
  obtain ⟨s,hs⟩ := (reduces_iff _ _).mp hdisjoint
  apply diagonalHalts_not_decidable
  refine ⟨numericalCompose (numericalProjectionTerm true) (evalProgram r),
    composeProgram_closed (projection_computes true).1 (evalProgram_closed r),fun e => ?_⟩
  obtain ⟨z,hz,hzQ⟩ := hr e e rfl
  have hout := composeProgram_runs (projection_computes true).1 (evalProgram_closed r)
    ((evalProgram_runs_iff r e z).mpr hz) ((projection_computes true).2 z)
  rcases hzQ with ⟨a,ha,rfl⟩ | ⟨b,hb,rfl⟩
  · have hh := (haltingPredicate_nonempty e).mp ⟨a,ha⟩
    simpa [hh] using hout
  · have hn : ¬ diagonalHalts e := by
      intro hh
      obtain ⟨a,ha⟩ := (haltingPredicate_nonempty e).mpr hh
      have hab : Nat.pair a b ∈ realizabilityAnd haltingPredicate Q e := by
        simpa [realizabilityAnd] using And.intro ha hb
      obtain ⟨c,_,hc⟩ := hs e (Nat.pair a b) hab
      exact hc
    simpa [hn] using hout

/-- Even with the input index available, excluded middle has no single realizer. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Take $Q:=H\to\bot$. Applying an implication realizer to a realizer of $H$ always tracks $H\land Q\le\bot$.
    A uniform realizer of the displayed formula would also track $E_N\le H\lor Q$, contrary to the proposition.
    More generally, the strict-predicate description of subobjects would make a complement of the subobject defined by
    $H$ satisfy exactly the two reductions in that proposition. This subobject has no complement,
    so the topos is not Boolean.
    The obstruction is uniformity; it does not deny the external classical alternative $e\in K$ or $e\notin K$ for each $e$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: corollary
  title: Failure of excluded middle
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
theorem halting_no_uniform_excluded_middle :
    ¬ Reduces naturalAssembly.realizes
      (realizabilityOr haltingPredicate (realizabilityImp haltingPredicate (realizabilityBot ℕ))) := by
  intro h
  apply halting_no_complement _ h
  apply reduces_trans (reduces_and_intro (reduces_and_right _ _) (reduces_and_left _ _))
  exact (reduces_imp_iff _ _ _).mpr (reduces_refl _)

end PolishSpaceBook.LambdaIndexPCA
