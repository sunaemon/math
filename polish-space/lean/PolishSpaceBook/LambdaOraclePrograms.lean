module

public import PolishSpaceBook.LambdaNumerals
public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Type-Two computation by lambda terms

A program is a closed term of the existing named lambda calculus modulo alpha.
The input name is passed as the distinguished free variable 0, whose applications
to Church numerals are answered by the name. Query reduction under an abstraction
requires a different binder, so a bound variable cannot be mistaken for the input.
No recursive-program code or externally supplied computability predicate occurs.
-/
namespace PolishSpaceBook
namespace NamedLambda.AlphaTerm

/-- Beta-reduction together with the behavior of the free input-name parameter. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Use ordinary untyped lambda calculus, identifying terms that differ only by renaming bound variables. Write
    $\ChurchNumeral{n}$ for the Church numeral representing $n$. A name $p:\NN\to\NN$ is supplied as a function argument:
    fix a free variable $o$ for that argument and add the query rule
    $$\LambdaInputStep{p}{o\ChurchNumeral{i}}{\ChurchNumeral{p(i)}}.$$
    Together with beta-reduction, this gives the one-step relation $\LambdaInputStep{p}{M}{N}$. Only free occurrences of $o$
    query the input; a bound occurrence retains its ordinary lambda-calculus meaning. As usual, bound variables may be
    renamed to avoid capture. These conventions suffice to use function arguments in the calculations below.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This appendix extends the numerical lambda calculus of §{sec:appendix-lambda-computability} to computation with
    an arbitrary input name. Baire space consists of the functions $\NN\to\NN$, with the product topology obtained
    from discrete $\NN$. An input name is supplied as a function argument; it need not be computable or finitely described.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a real parameter $a\in\BaireSpace$, identify $a$ with a function $\NN\to\NN$.
    \termdefineas{relativization}{Relativization} is the operation of allowing a fixed real parameter as background input. A
    \termdefine{program relative to a real} is a lambda program that may use $a$ as an input function and query values
    $a(n)$ during evaluation. This replaces the oracle-tape picture by the syntax that better matches later domain theory: a
    real parameter is an argument of function type, not a separate machine component.
-/
inductive OracleStep (p : ℕ → ℕ) : AlphaTerm → AlphaTerm → Prop where
  | beta {M N} : Beta M N → OracleStep p M N
  | query (n : ℕ) : OracleStep p (app (var 0) (numeral n)) (numeral (p n))
  | app_left {M M'} (N) : OracleStep p M M' → OracleStep p (app M N) (app M' N)
  | app_right (M) {N N'} : OracleStep p N N' → OracleStep p (app M N) (app M N')
  | lam (x : ℕ) (hx : x ≠ 0) {M M'} : OracleStep p M M' → OracleStep p (lam x M) (lam x M')

/-- A query can only occur through a free occurrence of the input parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  excerpt: |
    \begin{definition*}[Input-query computation and realization]
-/
theorem OracleStep.beta_or_input_free {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : OracleStep p M N) : Beta M N ∨ 0 ∈ M.fv := by
  induction h with
  | beta h => exact Or.inl h
  | query n =>
    right
    rw [fv_app]
    apply Finset.mem_union_left
    change 0 ∈ ({0} : Finset ℕ)
    simp
  | app_left N h ih =>
    rcases ih with hb | hf
    · exact Or.inl (.app_left N hb)
    · exact Or.inr (by rw [fv_app]; exact Finset.mem_union_left _ hf)
  | app_right M h ih =>
    rcases ih with hb | hf
    · exact Or.inl (.app_right M hb)
    · exact Or.inr (by rw [fv_app]; exact Finset.mem_union_right _ hf)
  | lam x hx h ih =>
    rcases ih with hb | hf
    · exact Or.inl (.lam x hb)
    · exact Or.inr (by rw [fv_lam]; exact Finset.mem_erase.mpr ⟨Ne.symm hx, hf⟩)

theorem OracleStep.beta_of_closed {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : OracleStep p M N) (hc : M.Closed) : Beta M N := by
  rcases h.beta_or_input_free with hb | hf
  · exact hb
  · rw [hc] at hf
    exact False.elim (Finset.notMem_empty _ hf)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  excerpt: |
    \begin{definition*}[Input-query computation and realization]
-/
theorem numeral_no_oracle_step (p : ℕ → ℕ) (n : ℕ) (N : AlphaTerm) :
    ¬ OracleStep p (numeral n) N :=
  fun h => numeral_normal n N (h.beta_of_closed (numeral_closed n))

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A program $\Phi$ is a closed lambda term. Given $p$ and a coordinate $n$, start with $\Phi\,o\,\ChurchNumeral{n}$. Write $\LambdaInputSteps{p}{M}{N}$ for a finite sequence of beta/query steps, including the empty sequence. We say that $\Phi$ returns $m$ on this input when
    $$
    \LambdaInputSteps{p}{\Phi\,o\,\ChurchNumeral{n}}{\ChurchNumeral{m}}.
    $$
    The name $p$ supplies query answers; it is not required to have a finite lambda description. Church numerals admit no further steps: they are closed beta-normal forms, and a query requires a free occurrence of the input parameter.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  excerpt: |
    \begin{definition*}[Input-query computation and realization]
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a real parameter $a\in\BaireSpace$, identify $a$ with a function $\NN\to\NN$.
    \termdefineas{relativization}{Relativization} is the operation of allowing a fixed real parameter as background input. A
    \termdefine{program relative to a real} is a lambda program that may use $a$ as an input function and query values
    $a(n)$ during evaluation. This replaces the oracle-tape picture by the syntax that better matches later domain theory: a
    real parameter is an argument of function type, not a separate machine component.
-/
def OracleRuns (p : ℕ → ℕ) (P : AlphaTerm) (n m : ℕ) : Prop :=
  Relation.ReflTransGen (OracleStep p) (app (app P (var 0)) (numeral n)) (numeral m)

theorem OracleStep.finite_use {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleStep p M N) :
    ∃ k, ∀ q : ℕ → ℕ, (∀ i < k, q i = p i) → OracleStep q M N := by
  induction h with
  | beta h => exact ⟨0, fun _ _ => .beta h⟩
  | query n =>
    refine ⟨n + 1, fun q hq => ?_⟩
    simpa only [hq n (Nat.lt_succ_self n)] using (OracleStep.query (p := q) n)
  | app_left N h ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, fun q hq => .app_left N (hk q hq)⟩
  | app_right M h ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, fun q hq => .app_right M (hk q hq)⟩
  | lam x hx h ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, fun q hq => .lam x hx (hk q hq)⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    A beta step needs no answers from the name. A query at coordinate $i$ is preserved by agreement below $i+1$. Moving either step into an allowed term context keeps the same bound. Now induct on the length of a finite reduction: the empty reduction needs no answers, and appending one step requires only the maximum of the bounds for the preceding reduction and the new step. Every name agreeing on this prefix therefore admits the same reduction to the same final term. This includes queries whose coordinates depend on earlier answers.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Finite use for input-query reductions
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The finite-use argument concerns a finite beta/query derivation of the lambda term itself. It does not require a
    translation into another programming language or a prescribed evaluation strategy.
-/
theorem oracle_steps_finite_use {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) :
    ∃ k, ∀ q : ℕ → ℕ, (∀ i < k, q i = p i) →
      Relation.ReflTransGen (OracleStep q) M N := by
  induction h with
  | refl => exact ⟨0, fun _ _ => .refl⟩
  | tail hs ht ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨l, hl⟩ := ht.finite_use
    exact ⟨max k l, fun q hq => .tail
      (hk q (fun i hi => hq i (hi.trans_le (le_max_left _ _))))
      (hl q (fun i hi => hq i (hi.trans_le (le_max_right _ _))))⟩

theorem OracleRuns.finite_use {p : ℕ → ℕ} {P : AlphaTerm} {n m : ℕ}
    (h : OracleRuns p P n m) :
    ∃ k, ∀ q : ℕ → ℕ, (∀ i < k, q i = p i) → OracleRuns q P n m :=
  oracle_steps_finite_use h

theorem isOpen_oracleRuns (P : AlphaTerm) (n m : ℕ) :
    IsOpen {p : ℕ → ℕ | OracleRuns p P n m} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨k, hk⟩ := hp.finite_use
  apply Filter.mem_of_superset ((isOpen_cyl (seqPrefix p k)).mem_nhds (mem_cyl_seqPrefix p k))
  intro q hq
  apply hk q
  intro i hi
  have he := seqPrefix_eq_of_mem_cyl hq
  have hev := congrArg (fun t : finseq ℕ => t.getD i 0) he
  simpa [seqPrefix, hi, List.getD_eq_getElem?_getD, seqPrefix_length] using hev

end NamedLambda.AlphaTerm
open NamedLambda NamedLambda.AlphaTerm

/-- One closed lambda term realizes the exact numerical graph on every valid name.
There is no requirement on names outside the specified domain. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termdefine{Type-Two lambda realizer} for a partial map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ is one closed term $\Phi$ such that, for every $p\in\DomainOf{F}$ and $n,m\in\NN$,
    $$
    \LambdaInputSteps{p}{\Phi\,o\,\ChurchNumeral{n}}{\ChurchNumeral{m}}
    \quad\Longleftrightarrow\quad F(p)(n)=m.
    $$
    Thus each output coordinate is obtained, and every numeral output has the specified value. No condition is imposed outside the domain. In particular, the domain may be smaller than the set of names on which all coordinate computations terminate. The same closed term must work for every valid name and every coordinate; choosing a different term separately for each name does not suffice. A partial map on names is called computable when it has such a realizer.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  excerpt: |
    \begin{definition*}[Input-query computation and realization]
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A point $p\in\BaireSpace$ is \termdefineas{computable point}{computable} if some index $e$ computes its digits, so
    $\varphi_e(n)=p(n)$ for every $n$. A partial map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ is a
    \termdefine{computable map on Baire space} if it has a Type-Two lambda realizer in the preceding definition. Thus the
    same closed term computes every output coordinate at every point of the specified domain. It may also produce outputs
    outside that domain.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The converse is false as stated: not every continuous map is computable. Even when finite-prefix bounds are effectively
    available, the output values themselves may contain non-computable information; for example, the constant map with value
    a non-computable point of Baire space is continuous with trivial modulus but is not computable. Computability is
    continuity together with an effective procedure which, from the requested coordinate and the finite input information
    used, produces the corresponding output value.
-/
def TypeTwoComputes (P : AlphaTerm) {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ)) : Prop :=
  P.Closed ∧ ∀ p n m, OracleRuns p.val P n m ↔ F p n = m

/-- Uniform Type-Two computability, with lambda terms as its only program syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A point $p\in\BaireSpace$ is \termdefineas{computable point}{computable} if some index $e$ computes its digits, so
    $\varphi_e(n)=p(n)$ for every $n$. A partial map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ is a
    \termdefine{computable map on Baire space} if it has a Type-Two lambda realizer in the preceding definition. Thus the
    same closed term computes every output coordinate at every point of the specified domain. It may also produce outputs
    outside that domain.
-/
def TypeTwoComputable {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ)) : Prop :=
  ∃ P, TypeTwoComputes P F

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: lemma
  title: Finite use and continuity
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Take a terminating computation at the given input and coordinate. It makes finitely many queries, including any
    addresses chosen from earlier answers. Choose $k$ larger than every queried address. A name agreeing on this prefix
    gives the same answers, so the same finite computation returns the same value.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The finite-use bound $k=k(p,n)$ is a local modulus of continuity.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The converse is false as stated: not every continuous map is computable. Even when finite-prefix bounds are effectively
    available, the output values themselves may contain non-computable information; for example, the constant map with value
    a non-computable point of Baire space is continuous with trivial modulus but is not computable. Computability is
    continuity together with an effective procedure which, from the requested coordinate and the finite input information
    used, produces the corresponding output value.
-/
theorem TypeTwoComputes.finite_use {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P : AlphaTerm} (h : TypeTwoComputes P F) (p : D) (n : ℕ) :
    ∃ k, ∀ q : D, (∀ i < k, q.val i = p.val i) → F q n = F p n := by
  obtain ⟨k, hk⟩ := ((h.2 p n (F p n)).mpr rfl).finite_use
  exact ⟨k, fun q hq => (h.2 q n (F p n)).mp (hk q.val hq)⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For a realizer and a fixed output coordinate, start with a reduction to its required numeral. Intersect the cylinder supplied by finite use with the specified name domain. At each name in this intersection, the same reduction still returns the original value, so the exact-output condition in the definition of a realizer makes the coordinate function constant there. It is therefore continuous into the discrete natural numbers. Continuity into Baire space is equivalent to continuity of every coordinate, which proves the assertion. Restricting the domain retains the same closed lambda term and needs no decision procedure for membership in the domain.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Every such map is continuous on its domain with the subspace topology. Indeed, fix a valid name and one coordinate.
    Finite use gives a cylinder on which the required numeral is still returned; intersect this cylinder with the domain.
    Output uniqueness makes the coordinate function constant there. All coordinates are therefore continuous into discrete
    $\NN$, which is equivalent to continuity into Baire space. Neither openness nor decidability of the domain is required.
-/
theorem TypeTwoComputes.continuous {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P : AlphaTerm} (h : TypeTwoComputes P F) : Continuous F := by
  apply continuous_pi
  intro n
  have h_fiber (v : ℕ) : IsOpen {p : D | F p n = v} := by
    convert (isOpen_oracleRuns P n v).preimage continuous_subtype_val using 1
    ext p
    exact (h.2 p n v).symm
  rw [continuous_def]
  intro U _
  rw [isOpen_iff_mem_nhds]
  intro p hp
  apply Filter.mem_of_superset ((h_fiber (F p n)).mem_nhds rfl)
  intro q hq
  change F q n ∈ U
  change F q n = F p n at hq
  change F p n ∈ U at hp
  simpa only [hq] using hp

theorem TypeTwoComputable.continuous {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    (h : TypeTwoComputable F) : Continuous F := by
  obtain ⟨P, hP⟩ := h
  exact hP.continuous

end PolishSpaceBook
