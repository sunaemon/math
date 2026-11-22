module

public import PolishSpaceBook.LambdaNumericalSections
public import PolishSpaceBook.LambdaBaireQuantifiers
public import PolishSpaceBook.LambdaUniformPredicates

@[expose] public section

/-! # Arithmetic formulas and relative pair-tree normal form

Finite Boolean combinations and numerical quantification start from predicates
with one total lambda decider on every input name. Numbers are bound by pairing
them with every input digit. Real existential quantification is separate.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance normalFormListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance normalFormPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Finite arithmetic formation; an atomic program ignores its auxiliary argument. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    A predicate is \termdefine{arithmetical relative to a real parameter} if it is obtained by finitely many
    Boolean operations and natural-number quantifiers from predicates decided by a single total lambda
    program on input $\NamePair{\varepsilon}{x}$. At each numerical quantifier, the new variable is encoded
    by $\NumberBinding{n}{x}$. Thus existential and universal quantification applied to a predicate $B$
    give $\exists n\ B(\NumberBinding{n}{x})$ and $\forall n\ B(\NumberBinding{n}{x})$.
    There is no bound on the finite number of quantifiers or their alternations. Quantification over
    infinite sequences is not part of this arithmetic formation rule.
-/
inductive ArithmeticalSet (ε : ℕ → ℕ) : Set (ℕ → ℕ) → Prop
  | atom (A : Set (ℕ → ℕ)) (P : AlphaTerm)
      (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P (fun _ : ℕ => x ∈ A)) :
      ArithmeticalSet ε A
  | compl {A} : ArithmeticalSet ε A → ArithmeticalSet ε Aᶜ
  | inter {A B} : ArithmeticalSet ε A → ArithmeticalSet ε B → ArithmeticalSet ε (A ∩ B)
  | existsNumber {A} : ArithmeticalSet ε A →
      ArithmeticalSet ε {x | ∃ n, bindNumber n x ∈ A}
  | forallNumber {A} : ArithmeticalSet ε A →
      ArithmeticalSet ε {x | ∀ n, bindNumber n x ∈ A}

theorem Projected.union {ε : ℕ → ℕ} {A B : Set (ℕ → ℕ)}
    (hA : Projected ε A) (hB : Projected ε B) : Projected ε (A ∪ B) := by
  obtain ⟨T,_,hT⟩ := (UniformProjected.const hA).union (UniformProjected.const hB)
  exact ⟨T 0,hT 0⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Induct on the finite formation of the predicate. For an atomic predicate, repeat its decision bit
    in every output coordinate and use the constant-one inverse-image construction of
    §{sec:edst-baire-quantifiers}. Reversing the decision bit handles its negation.
    Negation exchanges the two presentations. Conjunction uses intersection for the positive side and
    union for the negative side; disjunction follows by De Morgan's identity. For a numerical quantifier,
    apply the preceding lemma to both presentations: existential quantification uses union on the positive
    side and intersection on the negative side, and universal quantification reverses those roles.
    This proves every finite step without changing the parameter or requiring a computable choice of witnesses.
-/
theorem complemented_atom {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} {P : AlphaTerm}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P (fun _ : ℕ => x ∈ A)) :
    Complemented ε A := by
  have hp := projected_forall_baire hP
  have hn := projected_forall_baire
    (negatedBaireMatrix_decides (R := fun x _ _ => x ∈ A) hP)
  refine ⟨?_,?_⟩
  · simpa only [forall_const,Set.ofPred_mem_eq] using hp
  · convert hn using 1
    ext x
    simp

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Arithmetic predicates and their complements
-/
theorem ArithmeticalSet.complemented {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : ArithmeticalSet ε A) : Complemented ε A := by
  induction hA with
  | atom A P hP => exact complemented_atom hP
  | compl _ ih => exact ⟨ih.2,by simpa only [compl_compl] using ih.1⟩
  | inter _ _ ihA ihB =>
    exact ⟨ihA.1.inter ihB.1,by simpa only [compl_inter] using ihA.2.union ihB.2⟩
  | existsNumber _ ih => exact ih.existsNumber
  | forallNumber _ ih => exact ih.forallNumber

/-- A single existential real quantifier in front of a finite arithmetic formula. -/
def FormulaAnalytic (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  ∃ B, ArithmeticalSet ε B ∧ A = {x | ∃ q, pairBaire x q ∈ B}

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Suppose first that the displayed formula holds for an arithmetical predicate $B$. The preceding
    proposition presents $B$ by a relative pair tree.
    Project onto the first point coordinate as in §{sec:edst-coordinate-projections}; the omitted real
    and the tree witness are paired into one witness.

    Conversely, let $T$ present $A$. On a coded pair $z=\NamePair{x}{q}$, set
    $$B(z):\Longleftrightarrow\forall n\ (
     \restrict{x}{n},\restrict{q}{n})\in T.$$
    The row predicate is decidable uniformly from $\NumberBinding{n}{z}$ with parameter $\varepsilon$:
    read $n$, read exactly the first $n$ coordinates of $x$ and $q$, and pass their paired list codes
    to the decider for $T$. The finite-prefix reader and the accessors in
    §{sec:lambda-arithmetic-normal-form-programs} give one total closed term for this test.
    Thus $B$ is an atomic predicate followed by one universal natural-number quantifier, and the displayed
    existential-real formula says exactly that $x$ lies in the projection of $[T]$.
-/
theorem FormulaAnalytic.projected {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : FormulaAnalytic ε A) : Projected ε A := by
  obtain ⟨B,hB,rfl⟩ := hA
  convert hB.complemented.1.projectLeft using 1
  ext x
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨pairBaire x q,hq,by simp⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨rightBaire z,by simpa using hz⟩

/-- Input pairs the fixed parameter with a number bound to a point/witness pair. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the converse normal-form construction, write $\NumberBinding{n}{y}(k):=\NatPair{n}{y(k)}$.
    The input name is
    $\NamePair{\varepsilon}{\NumberBinding{n}{\NamePair{x}{q}}}$. Define the accessors
    $$\begin{aligned}
    D(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}(ok)},\\
    N(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    X(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))},\\
    Y(o)&:=\lambdaab{k}{\LambdaNumericProjection{2}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))}.
    \end{aligned}$$
    Using the finite-prefix reader, the closed row program is
    $$K:=\lambdaab{o}{\lambdaab{r}{P(D(o))(\LambdaNumericPair\,
     (\LambdaInputPrefix\,(X(o))\,(N(o)))\,
     (\LambdaInputPrefix\,(Y(o))\,(N(o))))}}.$$
    Expand the accessors with fresh binders. The auxiliary numerical argument $r$ is unused.
-/
def arithmeticRowBoundProgram : AlphaTerm := mapOutputProgram
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))
  (queryOutputProgram (constantProgram 0))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The paired-input equations show that $D,X,Y$ supply the parameter and the two sequences, while
    $N$ returns the bound number. The finite-prefix lemma therefore supplies exactly the two list codes
    for the first $n$ entries. Numerical pairing and substitution give the original tree decider its
    node code and its original parameter. This proves termination and both decision values by the
    same beta/query derivations. Quantifying over the bound number gives exactly the branch predicate.
    Reversing atomic decision bits and combining the presentations by the preceding countable-operation
    programs proves the forward construction for every finite arithmetic formula.
-/
theorem arithmeticRowBound_computes : UniformNumericalComputes arithmeticRowBoundProgram
    (fun p _ => leftBaire (rightBaire p) 0) := by
  exact (uniform_constant 0).query.map
    ((projection_computes true).comp (projection_computes false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the converse normal-form construction, write $\NumberBinding{n}{y}(k):=\NatPair{n}{y(k)}$.
    The input name is
    $\NamePair{\varepsilon}{\NumberBinding{n}{\NamePair{x}{q}}}$. Define the accessors
    $$\begin{aligned}
    D(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}(ok)},\\
    N(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    X(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))},\\
    Y(o)&:=\lambdaab{k}{\LambdaNumericProjection{2}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))}.
    \end{aligned}$$
    Using the finite-prefix reader, the closed row program is
    $$K:=\lambdaab{o}{\lambdaab{r}{P(D(o))(\LambdaNumericPair\,
     (\LambdaInputPrefix\,(X(o))\,(N(o)))\,
     (\LambdaInputPrefix\,(Y(o))\,(N(o))))}}.$$
    Expand the accessors with fresh binders. The auxiliary numerical argument $r$ is unused.
-/
def arithmeticRowCoordinateProgram (first : Bool) : AlphaTerm := mapOutputProgram
  (numericalCompose (numericalProjectionTerm first)
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))
  (queryOutputProgram (liftNumericalProgram numericalIdentity))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The paired-input equations show that $D,X,Y$ supply the parameter and the two sequences, while
    $N$ returns the bound number. The finite-prefix lemma therefore supplies exactly the two list codes
    for the first $n$ entries. Numerical pairing and substitution give the original tree decider its
    node code and its original parameter. This proves termination and both decision values by the
    same beta/query derivations. Quantifying over the bound number gives exactly the branch predicate.
    Reversing atomic decision bits and combining the presentations by the preceding countable-operation
    programs proves the forward construction for every finite arithmetic formula.
-/
theorem arithmeticRowCoordinate_computes (first : Bool) :
    UniformNumericalComputes (arithmeticRowCoordinateProgram first)
      (fun p k => if first then leftBaire (rightBaire (rightBaire p)) k
        else rightBaire (rightBaire (rightBaire p)) k) := by
  exact numericalIdentity_computes.uniform.query.map ((projection_computes first).comp
    ((projection_computes false).comp (projection_computes false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the converse normal-form construction, write $\NumberBinding{n}{y}(k):=\NatPair{n}{y(k)}$.
    The input name is
    $\NamePair{\varepsilon}{\NumberBinding{n}{\NamePair{x}{q}}}$. Define the accessors
    $$\begin{aligned}
    D(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}(ok)},\\
    N(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    X(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))},\\
    Y(o)&:=\lambdaab{k}{\LambdaNumericProjection{2}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))}.
    \end{aligned}$$
    Using the finite-prefix reader, the closed row program is
    $$K:=\lambdaab{o}{\lambdaab{r}{P(D(o))(\LambdaNumericPair\,
     (\LambdaInputPrefix\,(X(o))\,(N(o)))\,
     (\LambdaInputPrefix\,(Y(o))\,(N(o))))}}.$$
    Expand the accessors with fresh binders. The auxiliary numerical argument $r$ is unused.
-/
def arithmeticRowPrefixProgram (first : Bool) : AlphaTerm := relativeComposeProgram
  (compositionProgram prefixProgram (arithmeticRowCoordinateProgram first)) arithmeticRowBoundProgram

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The paired-input equations show that $D,X,Y$ supply the parameter and the two sequences, while
    $N$ returns the bound number. The finite-prefix lemma therefore supplies exactly the two list codes
    for the first $n$ entries. Numerical pairing and substitution give the original tree decider its
    node code and its original parameter. This proves termination and both decision values by the
    same beta/query derivations. Quantifying over the bound number gives exactly the branch predicate.
    Reversing atomic decision bits and combining the presentations by the preceding countable-operation
    programs proves the forward construction for every finite arithmetic formula.
-/
theorem arithmeticRowPrefix_computes (first : Bool) :
    UniformNumericalComputes (arithmeticRowPrefixProgram first) (fun p _ =>
      NatListCode.encode (seqPrefix
        (if first then leftBaire (rightBaire (rightBaire p)) else rightBaire (rightBaire (rightBaire p)))
        (leftBaire (rightBaire p) 0))) := by
  have hp : UniformNumericalComputes prefixProgram
      (fun p n => NatListCode.encode (seqPrefix p n)) := ⟨prefixProgram_closed,prefixProgram_runs⟩
  unfold arithmeticRowPrefixProgram
  convert (hp.changeInput (arithmeticRowCoordinate_computes first)).comp arithmeticRowBound_computes using 1
  funext p n
  cases first <;> rfl

def arithmeticRowInputProgram : AlphaTerm := pairOutputProgram
  (arithmeticRowPrefixProgram true) (arithmeticRowPrefixProgram false)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The paired-input equations show that $D,X,Y$ supply the parameter and the two sequences, while
    $N$ returns the bound number. The finite-prefix lemma therefore supplies exactly the two list codes
    for the first $n$ entries. Numerical pairing and substitution give the original tree decider its
    node code and its original parameter. This proves termination and both decision values by the
    same beta/query derivations. Quantifying over the bound number gives exactly the branch predicate.
    Reversing atomic decision bits and combining the presentations by the preceding countable-operation
    programs proves the forward construction for every finite arithmetic formula.
-/
theorem arithmeticRowInput_computes (ε y : ℕ → ℕ) :
    LambdaRelative.Computes (pairBaire ε y) arithmeticRowInputProgram
      (fun _ : ℕ => (seqPrefix (leftBaire (rightBaire y)) (leftBaire y 0),
        seqPrefix (rightBaire (rightBaire y)) (leftBaire y 0))) := by
  have h := (arithmeticRowPrefix_computes true).pair (arithmeticRowPrefix_computes false)
  refine ⟨h.1,fun n => ?_⟩
  simpa [Encodable.encode,arithmeticRowInputProgram] using h.2 (pairBaire ε y) n

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the converse normal-form construction, write $\NumberBinding{n}{y}(k):=\NatPair{n}{y(k)}$.
    The input name is
    $\NamePair{\varepsilon}{\NumberBinding{n}{\NamePair{x}{q}}}$. Define the accessors
    $$\begin{aligned}
    D(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}(ok)},\\
    N(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    X(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))},\\
    Y(o)&:=\lambdaab{k}{\LambdaNumericProjection{2}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))}.
    \end{aligned}$$
    Using the finite-prefix reader, the closed row program is
    $$K:=\lambdaab{o}{\lambdaab{r}{P(D(o))(\LambdaNumericPair\,
     (\LambdaInputPrefix\,(X(o))\,(N(o)))\,
     (\LambdaInputPrefix\,(Y(o))\,(N(o))))}}.$$
    Expand the accessors with fresh binders. The auxiliary numerical argument $r$ is unused.
-/
def arithmeticTreeRowProgram (P : AlphaTerm) : AlphaTerm := relativeComposeProgram
  (compositionProgram P (parameterProjectionProgram true)) arithmeticRowInputProgram

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The paired-input equations show that $D,X,Y$ supply the parameter and the two sequences, while
    $N$ returns the bound number. The finite-prefix lemma therefore supplies exactly the two list codes
    for the first $n$ entries. Numerical pairing and substitution give the original tree decider its
    node code and its original parameter. This proves termination and both decision values by the
    same beta/query derivations. Quantifying over the bound number gives exactly the branch predicate.
    Reversing atomic decision bits and combining the presentations by the preceding countable-operation
    programs proves the forward construction for every finite arithmetic formula.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the converse normal-form construction, write $\NumberBinding{n}{y}(k):=\NatPair{n}{y(k)}$.
    The input name is
    $\NamePair{\varepsilon}{\NumberBinding{n}{\NamePair{x}{q}}}$. Define the accessors
    $$\begin{aligned}
    D(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}(ok)},\\
    N(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    X(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))},\\
    Y(o)&:=\lambdaab{k}{\LambdaNumericProjection{2}
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))}.
    \end{aligned}$$
    Using the finite-prefix reader, the closed row program is
    $$K:=\lambdaab{o}{\lambdaab{r}{P(D(o))(\LambdaNumericPair\,
     (\LambdaInputPrefix\,(X(o))\,(N(o)))\,
     (\LambdaInputPrefix\,(Y(o))\,(N(o))))}}.$$
    Expand the accessors with fresh binders. The auxiliary numerical argument $r$ is unused.
-/
theorem arithmeticTreeRow_decides {ε : ℕ → ℕ} {T : Set (List ℕ × List ℕ)} {P : AlphaTerm}
    (hP : LambdaRelative.Decides ε P (fun z => z ∈ T)) :
    ∀ y, LambdaRelative.Decides (pairBaire ε y) (arithmeticTreeRowProgram P)
      (fun _ : ℕ => (seqPrefix (leftBaire (rightBaire y)) (leftBaire y 0),
        seqPrefix (rightBaire (rightBaire y)) (leftBaire y 0)) ∈ T) := by
  intro y
  exact (hP.changeParameter (parameterProjection_computes true ε y)).precomp
    (arithmeticRowInput_computes ε y)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Suppose first that the displayed formula holds for an arithmetical predicate $B$. The preceding
    proposition presents $B$ by a relative pair tree.
    Project onto the first point coordinate as in §{sec:edst-coordinate-projections}; the omitted real
    and the tree witness are paired into one witness.

    Conversely, let $T$ present $A$. On a coded pair $z=\NamePair{x}{q}$, set
    $$B(z):\Longleftrightarrow\forall n\ (
     \restrict{x}{n},\restrict{q}{n})\in T.$$
    The row predicate is decidable uniformly from $\NumberBinding{n}{z}$ with parameter $\varepsilon$:
    read $n$, read exactly the first $n$ coordinates of $x$ and $q$, and pass their paired list codes
    to the decider for $T$. The finite-prefix reader and the accessors in
    §{sec:lambda-arithmetic-normal-form-programs} give one total closed term for this test.
    Thus $B$ is an atomic predicate followed by one universal natural-number quantifier, and the displayed
    existential-real formula says exactly that $x$ lies in the projection of $[T]$.
-/
theorem arithmetical_pairTreeBody {ε : ℕ → ℕ} (T : PairTree ε) :
    ArithmeticalSet ε {z | (leftBaire z,rightBaire z) ∈ pairTreeBody T.tree} := by
  obtain ⟨P,hP⟩ := T.decidable
  have h := (ArithmeticalSet.atom _ (arithmeticTreeRowProgram P) (arithmeticTreeRow_decides hP)).forallNumber
  convert h using 1
  ext z
  change (∀ n, (seqPrefix (leftBaire z) n,seqPrefix (rightBaire z) n) ∈ T.tree) ↔
    ∀ n, (seqPrefix (leftBaire (rightBaire (bindNumber n z))) (leftBaire (bindNumber n z) 0),
      seqPrefix (rightBaire (rightBaire (bindNumber n z))) (leftBaire (bindNumber n z) 0)) ∈ T.tree
  simp only [leftBaire_bindNumber,rightBaire_bindNumber]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Suppose first that the displayed formula holds for an arithmetical predicate $B$. The preceding
    proposition presents $B$ by a relative pair tree.
    Project onto the first point coordinate as in §{sec:edst-coordinate-projections}; the omitted real
    and the tree witness are paired into one witness.

    Conversely, let $T$ present $A$. On a coded pair $z=\NamePair{x}{q}$, set
    $$B(z):\Longleftrightarrow\forall n\ (
     \restrict{x}{n},\restrict{q}{n})\in T.$$
    The row predicate is decidable uniformly from $\NumberBinding{n}{z}$ with parameter $\varepsilon$:
    read $n$, read exactly the first $n$ coordinates of $x$ and $q$, and pass their paired list codes
    to the decider for $T$. The finite-prefix reader and the accessors in
    §{sec:lambda-arithmetic-normal-form-programs} give one total closed term for this test.
    Thus $B$ is an atomic predicate followed by one universal natural-number quantifier, and the displayed
    existential-real formula says exactly that $x$ lies in the projection of $[T]$.
-/
theorem Projected.formulaAnalytic {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) : FormulaAnalytic ε A := by
  obtain ⟨T,rfl⟩ := hA
  refine ⟨_,arithmetical_pairTreeBody T,?_⟩
  ext x
  simp only [pairTreeProjection,Set.mem_ofPred_eq,leftBaire_pair,rightBaire_pair]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Arithmetic pair-tree normal form
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The correspondence between existential-real arithmetic formulas and relative pair-tree projections is proved
    in §{sec:edst-arithmetic-normal-form}. The proof keeps the same real parameter and allows any finite number
    of natural-number quantifiers.
-/
theorem formulaAnalytic_iff_projected (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    FormulaAnalytic ε A ↔ Projected ε A := ⟨FormulaAnalytic.projected,Projected.formulaAnalytic⟩

end LambdaTree
end PolishSpaceBook
