module

public import PolishSpaceBook.LambdaNumericalQueries
public import PolishSpaceBook.LambdaSyntaxCoding
public import PolishSpaceBook.LambdaNumericalSearch

@[expose] public section

/-! # Predicate computation relative to a fixed real parameter

Programs are closed lambda terms, evaluated by beta/query reduction with one
fixed input function. Natural-number indices come from named lambda syntax.
No oracle-recursive language or cross-model simulation is used.
-/
namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm Encodable Set
universe u v

/-- Relative computation on specified numerical encodings; no behavior is
required on numbers that do not encode an input. -/
def Computes {α : Type u} {β : Type v} [Encodable α] [Encodable β]
    (ε : ℕ → ℕ) (P : AlphaTerm) (f : α → β) : Prop :=
  P.Closed ∧ ∀ a, OracleRuns ε P (encode a) (encode (f a))

def Computable {α : Type u} {β : Type v} [Encodable α] [Encodable β]
    (ε : ℕ → ℕ) (f : α → β) : Prop := ∃ P, Computes ε P f

/-- Both answers are numeral outputs, so the decider is total on encoded inputs. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Throughout the effective arguments, a program is a finite lambda term. Fix a real parameter
    $\varepsilon:\NN\to\NN$ and a numerical coding of the inputs. A program may query $\varepsilon(n)$ while
    performing beta reduction, as defined in §{sec:lambda-input-realizers}. A predicate on the coded inputs is
    \emph{decidable relative to $\varepsilon$} when one closed term terminates on every valid input code and returns
    one if the predicate holds and zero otherwise. The parameter is fixed throughout the computation and throughout
    any argument using the same relative pointclass. No behavior is prescribed on numbers that are not valid input
    codes. The lambda terms and their numerical indices are described in §{sec:lambda-syntax-codes}.
-/
def Decides {α : Type u} [Encodable α] (ε : ℕ → ℕ) (P : AlphaTerm) (R : α → Prop) : Prop :=
  P.Closed ∧ ∀ a, (R a → OracleRuns ε P (encode a) 1) ∧
    (¬ R a → OracleRuns ε P (encode a) 0)

def DecidablePredicate {α : Type u} [Encodable α] (ε : ℕ → ℕ) (R : α → Prop) : Prop :=
  ∃ P, Decides ε P R

theorem Computes.unique {α : Type u} {β : Type v} [Encodable α] [Encodable β]
    {ε : ℕ → ℕ} {P : AlphaTerm} {f g : α → β}
    (hf : Computes ε P f) (hg : Computes ε P g) : f = g := by
  funext a
  exact Encodable.encode_injective ((hf.2 a).output_unique (hg.2 a))

theorem Decides.unique {α : Type u} [Encodable α] {ε : ℕ → ℕ} {P : AlphaTerm}
    {R S : α → Prop} (hR : Decides ε P R) (hS : Decides ε P S) : R = S := by
  classical
  funext a
  apply propext
  constructor
  · intro hr
    by_contra hs
    have h := (hR.2 a).1 hr |>.output_unique ((hS.2 a).2 hs)
    omega
  · intro hs
    by_contra hr
    have h := (hS.2 a).1 hs |>.output_unique ((hR.2 a).2 hr)
    omega

theorem Decides.runs {α : Type u} [Encodable α] {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : α → Prop} (hR : Decides ε P R) (a : α) [Decidable (R a)] :
    OracleRuns ε P (encode a) (if R a then 1 else 0) := by
  split_ifs with h
  · exact (hR.2 a).1 h
  · exact (hR.2 a).2 h

/-- Pull a decision back through an actual numerical code transformation. -/
theorem Decides.precompNumerical {α : Type u} {β : Type v}
    [Encodable α] [Encodable β] {ε : ℕ → ℕ} {P F : AlphaTerm}
    {R : β → Prop} {g : α → β} {f : ℕ → ℕ}
    (hP : Decides ε P R) (hF : NumericalComputes F f)
    (hf : ∀ a, f (encode a) = encode (g a)) :
    Decides ε (reindexProgram P F) (fun a => R (g a)) := by
  refine ⟨reindexProgram_closed hP.1 hF.1,fun a => ⟨?_,?_⟩⟩
  · intro h
    exact reindexProgram_runs hP.1 hF.1 ε _ _ _
      (hf a ▸ hF.2 (encode a)) ((hP.2 (g a)).1 h)
  · intro h
    exact reindexProgram_runs hP.1 hF.1 ε _ _ _
      (hf a ▸ hF.2 (encode a)) ((hP.2 (g a)).2 h)

theorem DecidablePredicate.precompNumerical {α : Type u} {β : Type v}
    [Encodable α] [Encodable β] {ε : ℕ → ℕ} {F : AlphaTerm}
    {R : β → Prop} {g : α → β} {f : ℕ → ℕ}
    (hR : DecidablePredicate ε R) (hF : NumericalComputes F f)
    (hf : ∀ a, f (encode a) = encode (g a)) :
    DecidablePredicate ε (fun a => R (g a)) := by
  obtain ⟨P,hP⟩ := hR
  exact ⟨_,hP.precompNumerical hF hf⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Let $P,Q$ decide the two predicates. For complement, compute the output of $P$ and apply the closed numerical term
    that returns one on zero and zero on a positive input. For intersection, compute both outputs and multiply them.
    The multiplication term returns one exactly when both answers are one. Beta/query reductions lift through the
    application contexts, and both component computations terminate on every valid input code. These
    compositions are closed because their component terms are closed and their input variables are bound.
    Iterating intersection handles any nonempty finite family; the constant-one program handles the empty family.
-/
theorem DecidablePredicate.not {α : Type u} [Encodable α] {ε : ℕ → ℕ} {R : α → Prop}
    (hR : DecidablePredicate ε R) : DecidablePredicate ε (fun a => ¬ R a) := by
  classical
  obtain ⟨P,hP⟩ := hR
  refine ⟨mapOutputProgram reverseZeroTerm P,
    mapOutputProgram_closed reverseZero_computes.1 hP.1,fun a => ⟨?_,?_⟩⟩
  · intro h
    exact mapOutputProgram_runs reverseZero_computes.1 hP.1 ((hP.2 a).2 h)
      (by simpa using reverseZero_computes.2 0)
  · intro h
    exact mapOutputProgram_runs reverseZero_computes.1 hP.1 ((hP.2 a).1 (not_not.mp h))
      (by simpa using reverseZero_computes.2 1)

theorem DecidablePredicate.and {α : Type u} [Encodable α] {ε : ℕ → ℕ}
    {R S : α → Prop} (hR : DecidablePredicate ε R) (hS : DecidablePredicate ε S) :
    DecidablePredicate ε (fun a => R a ∧ S a) := by
  classical
  obtain ⟨P,hP⟩ := hR
  obtain ⟨Q,hQ⟩ := hS
  let M := mulNumerical (numericalProjectionTerm true) (numericalProjectionTerm false)
  have hM : NumericalComputes M (fun z => z.unpair.1 * z.unpair.2) :=
    (projection_computes true).mul (projection_computes false)
  refine ⟨mapOutputProgram M (pairOutputProgram P Q),
    mapOutputProgram_closed hM.1 (pairOutputProgram_closed hP.1 hQ.1),fun a => ?_⟩
  have hr := mapOutputProgram_runs hM.1 (pairOutputProgram_closed hP.1 hQ.1)
    (pairOutputProgram_runs hP.1 hQ.1 (hP.runs a) (hQ.runs a))
    (hM.2 (Nat.pair (if R a then 1 else 0) (if S a then 1 else 0)))
  simp only [Nat.unpair_pair] at hr
  constructor
  · rintro ⟨ha,hb⟩
    simpa only [ite_eq_left ha,ite_eq_left hb,mul_one] using hr
  · intro h
    by_cases ha : R a
    · have hb : ¬ S a := fun hb => h ⟨ha,hb⟩
      simpa only [ite_eq_left ha,ite_eq_right hb,mul_zero] using hr
    · simpa only [ite_eq_right ha,zero_mul] using hr

theorem decidablePredicate_true (α : Type u) [Encodable α] (ε : ℕ → ℕ) :
    DecidablePredicate ε (fun _ : α => True) := by
  refine ⟨constantProgram 1,constantProgram_closed 1,fun a => ⟨?_,?_⟩⟩
  · intro _; exact constantProgram_runs 1 ε (encode a)
  · intro h; exact (h trivial).elim

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Relative Boolean decision programs
-/
theorem DecidablePredicate.finset_all {α : Type u} [Encodable α] {ι : Type v}
    {ε : ℕ → ℕ} {R : ι → α → Prop} (s : Finset ι)
    (hR : ∀ i ∈ s, DecidablePredicate ε (R i)) :
    DecidablePredicate ε (fun a => ∀ i ∈ s, R i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using decidablePredicate_true α ε
  | @insert i s hi ih =>
    simpa only [Finset.mem_insert,forall_eq_or_imp] using
      (hR i (Finset.mem_insert_self i s)).and
        (ih (fun j hj => hR j (Finset.mem_insert_of_mem hj)))

/-- Choose a syntax index, without asserting that valid indices are decidable. -/
theorem Computable.exists_index {α : Type u} {β : Type v} [Encodable α] [Encodable β]
    {ε : ℕ → ℕ} {f : α → β} (hf : Computable ε f) :
    ∃ e, Computes ε (Term.closedProgram e) f := by
  obtain ⟨P,hP⟩ := hf
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP.1
  exact ⟨e,he ▸ hP⟩

theorem DecidablePredicate.exists_index {α : Type u} [Encodable α]
    {ε : ℕ → ℕ} {R : α → Prop} (hR : DecidablePredicate ε R) :
    ∃ e, Decides ε (Term.closedProgram e) R := by
  obtain ⟨P,hP⟩ := hR
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP.1
  exact ⟨e,he ▸ hP⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Countability of relative predicates
-/
theorem countable_computable (α : Type u) (β : Type v) [Encodable α] [Encodable β]
    (ε : ℕ → ℕ) : Countable {f : α → β // Computable ε f} := by
  classical
  let code (f : {f : α → β // Computable ε f}) : ℕ := f.property.exists_index.choose
  apply Function.Injective.countable (f := code)
  intro f g h
  apply Subtype.ext
  have hf := f.property.exists_index.choose_spec
  have hg := g.property.exists_index.choose_spec
  change code f = code g at h
  change Computes ε (Term.closedProgram (code f)) f.val at hf
  change Computes ε (Term.closedProgram (code g)) g.val at hg
  rw [h] at hf
  exact hf.unique hg

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Every closed lambda term has a natural-number syntax index. With the parameter fixed, uniqueness of numerical
    outputs implies that one index computes at most one function on the specified input set, and decides at most
    one predicate there. Choose one index for each function or predicate. Equal chosen indices imply equal values
    on every input, so this assignment is injective into $\NN$. This proves countability; it does not give an algorithm
    for recognizing the indices that terminate on all valid inputs.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For completeness, the countability assertion in §{sec:edst-relative-programs} uses the syntax coding already
    constructed here. Every closed alpha-class has a named representative and hence a natural-number program index.
    Choose such an index for each relatively computable function or predicate. If two chosen indices coincide,
    output uniqueness applied with the same parameter and input code equates their numerical outputs. Injectivity
    of the output coding equates function values; for predicates, opposite truth values would give the distinct
    outputs zero and one. Thus each assignment of indices is injective.
-/
theorem countable_decidablePredicates (α : Type u) [Encodable α] (ε : ℕ → ℕ) :
    Countable {R : α → Prop // DecidablePredicate ε R} := by
  classical
  let code (R : {R : α → Prop // DecidablePredicate ε R}) : ℕ := R.property.exists_index.choose
  apply Function.Injective.countable (f := code)
  intro R S h
  apply Subtype.ext
  have hR := R.property.exists_index.choose_spec
  have hS := S.property.exists_index.choose_spec
  change code R = code S at h
  change Decides ε (Term.closedProgram (code R)) R.val at hR
  change Decides ε (Term.closedProgram (code S)) S.val at hS
  rw [h] at hR
  exact hR.unique hS

/-- A fixed row is read by a closed lambda term using one paired query. -/
def rowProgram (i : ℕ) : AlphaTerm :=
  queryOutputProgram (liftNumericalProgram (pairNumerical (numericalConstant i) numericalIdentity))

theorem rowProgram_computes (i : ℕ) :
    UniformNumericalComputes (rowProgram i) (fun ε n => ε (Nat.pair i n)) :=
  ((numericalConstant_computes i).pair numericalIdentity_computes).uniform.query

/-- One real parameter encodes every predicate in any specified countable family. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: A common parameter for countably many predicates
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Use the numerical pairing of §{sec:lambda-numerical-pairing}. For each $z\in S$, give the parameter value one
    at the pair of $i$ and $c(z)$ exactly when $R_i(z)$ holds, and zero at every other coordinate.
    Injectivity of the coding makes this definition unambiguous. For fixed $i$, a closed program pairs the numeral
    for $i$ with the supplied input code,
    queries that coordinate, and returns the answer. Numerical pairing is computed by a closed lambda term, so this
    is an actual program using the chosen parameter. The construction puts all the predicates' truth values into
    that parameter; it does not assert that the parameter itself is computable. The explicit row-reading term is
    given in §{sec:lambda-relative-predicates}.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For a sequence of predicates $R_i$ on $S$, define a parameter $\varepsilon$ by
    $$
    \varepsilon(\NatPair{i}{n})=
    \begin{cases}
    1,&\exists s\in S\ (c(s)=n\ \land\ R_i(s)),\\
    0,&\text{otherwise}.
    \end{cases}
    $$
    The fixed row $i$ is read by the closed term
    $$P_i:=\lambdaab{o}{\lambdaab{z}{o\bigl(\LambdaNumericPair\,\ChurchNumeral{i}\,z\bigr)}}.$$
    Two beta steps, the numerical pairing reduction, and one input query return
    $\ChurchNumeral{\varepsilon(\NatPair{i}{c(s)})}$ on input code $c(s)$. Injectivity of $c$ makes this numeral one
    exactly when $R_i(s)$ holds, and zero otherwise. This proves the common-parameter proposition of
    §{sec:edst-relative-programs} with an explicit program for each row. The parameter may be noncomputable.
-/
theorem predicates_in_one_parameter {α : Type u} [Encodable α] (R : ℕ → α → Prop) :
    ∃ ε : ℕ → ℕ, ∀ i, Decides ε (rowProgram i) (R i) := by
  classical
  let ε : ℕ → ℕ := fun z =>
    if ∃ a, decode (α := α) z.unpair.2 = some a ∧ R z.unpair.1 a then 1 else 0
  refine ⟨ε,fun i => ⟨(rowProgram_computes i).1,fun a => ⟨?_,?_⟩⟩⟩
  · intro ha
    simpa [ε, Nat.unpair_pair, ha] using (rowProgram_computes i).2 ε (encode a)
  · intro ha
    simpa [ε, Nat.unpair_pair, ha] using (rowProgram_computes i).2 ε (encode a)

end PolishSpaceBook.LambdaRelative
