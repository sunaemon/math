module

public import PolishSpaceBook.LambdaBorelExternalValidity
public import PolishSpaceBook.LambdaProgramTotality

@[expose] public section

/-! # Coanalytic validity for arbitrary lambda program indices

Partial programs are handled explicitly. Computation-table witnesses carry an
output and a finite verification bound for each numerical input.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace BorelExpression
open LambdaRelative
local instance indexValidityListEncoding : Encodable (List ℕ) := NatListCode.encodable

def ComputationTable (ε : ℕ → ℕ) (e : ℕ) (q : ℕ → ℕ) : Prop :=
  ∀ n, Term.oracleOutputCandidate ε e n (q n) = true

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    At parameter $\varepsilon$, a numerical index $e$ is a \termdefine{valid Borel-expression program index}
    if its program returns a numeral on every input $\LambdaListCode{s}$ and the resulting label map is
    a valid Borel expression.
-/
def ValidProgramIndex (ε : ℕ → ℕ) (e : ℕ) : Prop :=
  ∃ c : BorelExpression, Computes ε (Term.closedProgram e) c ∧ c.Valid

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
    §{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
    $$v(n)=\NatPair{m_n}{r_n},\qquad
    \Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
    Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
    even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
    therefore gives a tree presentation of the relation between an index code and an accepted table,
    by the universal-row construction.

    Decode the table as the label map
    $$h_v(s):=m_{\LambdaListCode{s}}.$$
    Soundness of the candidate tests shows that the indexed program computes this map whenever
    $\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
    candidate for each input; choosing them gives a table. This is an existence statement, not an
    algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
    accepted table has the same decoded labels as the program's output.

    The map extracting the output sequence from a table uses only numerical pair projections. Pull back
    the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
    onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
    table whose decoded expression is invalid.

    Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
    set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
    do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
    and in the latter case its decoded expression must be invalid. This proves the claimed complement
    representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
-/
theorem computationTable_computes {ε q : ℕ → ℕ} {e : ℕ} (hq : ComputationTable ε e q) :
    Computes ε (Term.closedProgram e) (streamLabels (leftBaire q)) := by
  refine ⟨Term.closedProgram_closed e,fun s => ?_⟩
  apply (oracle_outputTest_exists_iff ε e (NatListCode.encode s) _).mp
  refine ⟨(q (NatListCode.encode s)).unpair.2,?_⟩
  simpa only [Term.oracleOutputCandidate,Encodable.encode_nat,streamLabels,leftBaire] using
    hq (NatListCode.encode s)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
    §{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
    $$v(n)=\NatPair{m_n}{r_n},\qquad
    \Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
    Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
    even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
    therefore gives a tree presentation of the relation between an index code and an accepted table,
    by the universal-row construction.

    Decode the table as the label map
    $$h_v(s):=m_{\LambdaListCode{s}}.$$
    Soundness of the candidate tests shows that the indexed program computes this map whenever
    $\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
    candidate for each input; choosing them gives a table. This is an existence statement, not an
    algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
    accepted table has the same decoded labels as the program's output.

    The map extracting the output sequence from a table uses only numerical pair projections. Pull back
    the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
    onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
    table whose decoded expression is invalid.

    Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
    set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
    do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
    and in the latter case its decoded expression must be invalid. This proves the claimed complement
    representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
-/
theorem computationTable_exists_of_total {ε : ℕ → ℕ} {e : ℕ}
    (he : LambdaTree.TotalIndex ε e) : ∃ q, ComputationTable ε e q := by
  have h := (LambdaTree.totalIndex_iff_candidates ε e).mp he
  exact Classical.skolem.mp h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
    §{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
    $$v(n)=\NatPair{m_n}{r_n},\qquad
    \Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
    Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
    even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
    therefore gives a tree presentation of the relation between an index code and an accepted table,
    by the universal-row construction.

    Decode the table as the label map
    $$h_v(s):=m_{\LambdaListCode{s}}.$$
    Soundness of the candidate tests shows that the indexed program computes this map whenever
    $\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
    candidate for each input; choosing them gives a table. This is an existence statement, not an
    algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
    accepted table has the same decoded labels as the program's output.

    The map extracting the output sequence from a table uses only numerical pair projections. Pull back
    the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
    onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
    table whose decoded expression is invalid.

    Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
    set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
    do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
    and in the latter case its decoded expression must be invalid. This proves the claimed complement
    representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    List coding is bijective, so the totality requirement covers every numerical input.
-/
theorem validProgramIndex_total {ε : ℕ → ℕ} {e : ℕ} (he : ValidProgramIndex ε e) :
    LambdaTree.TotalIndex ε e := by
  obtain ⟨c,hc,_⟩ := he
  intro n
  refine ⟨c (NatListCode.decode n),?_⟩
  simpa [Encodable.encode] using hc.2 (NatListCode.decode n)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
    §{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
    $$v(n)=\NatPair{m_n}{r_n},\qquad
    \Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
    Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
    even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
    therefore gives a tree presentation of the relation between an index code and an accepted table,
    by the universal-row construction.

    Decode the table as the label map
    $$h_v(s):=m_{\LambdaListCode{s}}.$$
    Soundness of the candidate tests shows that the indexed program computes this map whenever
    $\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
    candidate for each input; choosing them gives a table. This is an existence statement, not an
    algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
    accepted table has the same decoded labels as the program's output.

    The map extracting the output sequence from a table uses only numerical pair projections. Pull back
    the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
    onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
    table whose decoded expression is invalid.

    Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
    set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
    do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
    and in the latter case its decoded expression must be invalid. This proves the claimed complement
    representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
-/
theorem not_validProgramIndex_iff (ε : ℕ → ℕ) (e : ℕ) :
    ¬ ValidProgramIndex ε e ↔ ¬ LambdaTree.TotalIndex ε e ∨
      ∃ q, ComputationTable ε e q ∧ ¬ (streamLabels (leftBaire q)).Valid := by
  classical
  constructor
  · intro he
    by_cases ht : LambdaTree.TotalIndex ε e
    · obtain ⟨q,hq⟩ := computationTable_exists_of_total ht
      exact Or.inr ⟨q,hq,fun hv => he ⟨_,computationTable_computes hq,hv⟩⟩
    · exact Or.inl ht
  · rintro (ht | ⟨q,hq,hbad⟩) hvalid
    · exact ht (validProgramIndex_total hvalid)
    · obtain ⟨c,hc,hv⟩ := hvalid
      have heq := (computationTable_computes hq).unique hc
      exact hbad (heq ▸ hv)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
    $\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
    $$\begin{aligned}
    \LambdaTermName{parameterInput}(o)&:=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
    \LambdaTermName{inputIndex}(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{candidateTrial}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaQueryOutputCandidate\,(
    \LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,n\,(
    \LambdaTermName{witnessEntry}(o,n))}}.
    \end{aligned}$$
    The decoded output sequence is read by
    $$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
    \LambdaTermName{witnessEntry}(o,n))}}.$$
    All these are closed terms after expanding the abbreviations and choosing fresh binders.
-/
def tableParameterProgram : AlphaTerm := mapOutputProgram (numericalProjectionTerm true)
  (queryOutputProgram (liftNumericalProgram numericalIdentity))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem tableParameterProgram_computes : UniformNumericalComputes tableParameterProgram leftBaire := by
  exact numericalIdentity_computes.uniform.query.map (projection_computes true)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
    $\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
    $$\begin{aligned}
    \LambdaTermName{parameterInput}(o)&:=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
    \LambdaTermName{inputIndex}(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{candidateTrial}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaQueryOutputCandidate\,(
    \LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,n\,(
    \LambdaTermName{witnessEntry}(o,n))}}.
    \end{aligned}$$
    The decoded output sequence is read by
    $$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
    \LambdaTermName{witnessEntry}(o,n))}}.$$
    All these are closed terms after expanding the abbreviations and choosing fresh binders.
-/
def tableIndexProgram : AlphaTerm := mapOutputProgram
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))
  (queryOutputProgram (constantProgram 0))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem tableIndexProgram_computes : UniformNumericalComputes tableIndexProgram
    (fun p _ => leftBaire (rightBaire p) 0) := by
  exact (uniform_constant 0).query.map
    ((projection_computes true).comp (projection_computes false))

def tableWitnessProgram : AlphaTerm := mapOutputProgram
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
  (queryOutputProgram (liftNumericalProgram numericalIdentity))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem tableWitnessProgram_computes : UniformNumericalComputes tableWitnessProgram
    (fun p n => rightBaire (rightBaire p) n) := by
  exact numericalIdentity_computes.uniform.query.map
    ((projection_computes false).comp (projection_computes false))

/-- Read the output component of a supplied candidate; no table is selected. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
    $\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
    $$\begin{aligned}
    \LambdaTermName{parameterInput}(o)&:=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
    \LambdaTermName{inputIndex}(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{candidateTrial}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaQueryOutputCandidate\,(
    \LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,n\,(
    \LambdaTermName{witnessEntry}(o,n))}}.
    \end{aligned}$$
    The decoded output sequence is read by
    $$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
    \LambdaTermName{witnessEntry}(o,n))}}.$$
    All these are closed terms after expanding the abbreviations and choosing fresh binders.
-/
def tableOutputProgram : AlphaTerm :=
  mapOutputProgram (numericalProjectionTerm true) tableWitnessProgram

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
    $\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
    $$\begin{aligned}
    \LambdaTermName{parameterInput}(o)&:=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
    \LambdaTermName{inputIndex}(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{candidateTrial}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaQueryOutputCandidate\,(
    \LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,n\,(
    \LambdaTermName{witnessEntry}(o,n))}}.
    \end{aligned}$$
    The decoded output sequence is read by
    $$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
    \LambdaTermName{witnessEntry}(o,n))}}.$$
    All these are closed terms after expanding the abbreviations and choosing fresh binders.
-/
theorem tableOutputProgram_computes : UniformNumericalComputes tableOutputProgram
    (fun p n => (rightBaire (rightBaire p) n).unpair.1) :=
  tableWitnessProgram_computes.map (projection_computes true)

def tableArgumentProgram : AlphaTerm := pairOutputProgram tableIndexProgram
  (pairOutputProgram (liftNumericalProgram numericalIdentity) tableWitnessProgram)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem tableArgumentProgram_computes : UniformNumericalComputes tableArgumentProgram
    (fun p n => Nat.pair (leftBaire (rightBaire p) 0) (Nat.pair n (rightBaire (rightBaire p) n))) :=
  tableIndexProgram_computes.pair (numericalIdentity_computes.uniform.pair tableWitnessProgram_computes)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
    $\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
    $$\begin{aligned}
    \LambdaTermName{parameterInput}(o)&:=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
    \LambdaTermName{inputIndex}(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{candidateTrial}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaQueryOutputCandidate\,(
    \LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,n\,(
    \LambdaTermName{witnessEntry}(o,n))}}.
    \end{aligned}$$
    The decoded output sequence is read by
    $$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
    \LambdaTermName{witnessEntry}(o,n))}}.$$
    All these are closed terms after expanding the abbreviations and choosing fresh binders.
-/
def tableCandidateProgram : AlphaTerm := relativeComposeProgram
  (compositionProgram jointCandidateProgram tableParameterProgram) tableArgumentProgram

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
    $\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
    $$\begin{aligned}
    \LambdaTermName{parameterInput}(o)&:=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
    \LambdaTermName{inputIndex}(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{candidateTrial}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaQueryOutputCandidate\,(
    \LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,n\,(
    \LambdaTermName{witnessEntry}(o,n))}}.
    \end{aligned}$$
    The decoded output sequence is read by
    $$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
    \LambdaTermName{witnessEntry}(o,n))}}.$$
    All these are closed terms after expanding the abbreviations and choosing fresh binders.
-/
theorem tableCandidateProgram_computes : UniformNumericalComputes tableCandidateProgram
    (fun p n => if Term.oracleOutputCandidate (leftBaire p) (leftBaire (rightBaire p) 0)
      n (rightBaire (rightBaire p) n) then 1 else 0) := by
  simpa only [tableCandidateProgram,Nat.unpair_pair] using
    (jointCandidateProgram_computes.changeInput tableParameterProgram_computes).comp
      tableArgumentProgram_computes

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem uniform_computationTableRow : UniformDecidablePredicate (fun p (n : ℕ) =>
    Term.oracleOutputCandidate (leftBaire p) (leftBaire (rightBaire p) 0)
      n (rightBaire (rightBaire p) n) = true) := by
  refine ⟨tableCandidateProgram,fun p => ⟨tableCandidateProgram_computes.1,fun n => ⟨?_,?_⟩⟩⟩ <;> intro hn
  · simpa [hn] using tableCandidateProgram_computes.2 p n
  · simpa [hn] using tableCandidateProgram_computes.2 p n

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
    §{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
    $$v(n)=\NatPair{m_n}{r_n},\qquad
    \Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
    Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
    even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
    therefore gives a tree presentation of the relation between an index code and an accepted table,
    by the universal-row construction.

    Decode the table as the label map
    $$h_v(s):=m_{\LambdaListCode{s}}.$$
    Soundness of the candidate tests shows that the indexed program computes this map whenever
    $\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
    candidate for each input; choosing them gives a table. This is an existence statement, not an
    algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
    accepted table has the same decoded labels as the program's output.

    The map extracting the output sequence from a table uses only numerical pair projections. Pull back
    the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
    onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
    table whose decoded expression is invalid.

    Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
    set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
    do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
    and in the latter case its decoded expression must be invalid. This proves the claimed complement
    representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
-/
theorem projected_computationTables (ε : ℕ → ℕ) :
    LambdaTree.Projected ε {z | ComputationTable ε (leftBaire z 0) (rightBaire z)} := by
  obtain ⟨P,hP⟩ := uniform_computationTableRow
  have hh : ∀ z, Decides (pairBaire ε z) P (fun n =>
      Term.oracleOutputCandidate ε (leftBaire z 0) n (rightBaire z n) = true) := by
    intro z
    simpa only [leftBaire_pair,rightBaire_pair] using hP (pairBaire ε z)
  exact LambdaTree.projected_forall_baire hh

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
    §{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
    $$v(n)=\NatPair{m_n}{r_n},\qquad
    \Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
    Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
    even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
    therefore gives a tree presentation of the relation between an index code and an accepted table,
    by the universal-row construction.

    Decode the table as the label map
    $$h_v(s):=m_{\LambdaListCode{s}}.$$
    Soundness of the candidate tests shows that the indexed program computes this map whenever
    $\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
    candidate for each input; choosing them gives a table. This is an existence statement, not an
    algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
    accepted table has the same decoded labels as the program's output.

    The map extracting the output sequence from a table uses only numerical pair projections. Pull back
    the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
    onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
    table whose decoded expression is invalid.

    Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
    set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
    do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
    and in the latter case its decoded expression must be invalid. This proves the claimed complement
    representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
-/
theorem projected_badComputationTables (ε : ℕ → ℕ) :
    LambdaTree.Projected ε {x | ∃ q, ComputationTable ε (x 0) q ∧
      ¬ (streamLabels (leftBaire q)).Valid} := by
  have hbad := (projected_streamNotValid ε).coordinatePreimage
    ((projection_computes true).comp (projection_computes false))
  have hbad' : LambdaTree.Projected ε
      {z | ¬ (streamLabels (leftBaire (rightBaire z))).Valid} := by
    convert hbad using 1
    ext z
    rfl
  have h := ((projected_computationTables ε).inter hbad').projectLeft
  convert h using 1
  ext x
  constructor
  · rintro ⟨q,hq,hb⟩
    exact ⟨pairBaire x q,⟨by simpa using hq,by simpa using hb⟩,by simp⟩
  · rintro ⟨z,⟨hq,hb⟩,rfl⟩
    exact ⟨rightBaire z,hq,hb⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Coanalytic validity of Borel-expression program indices
-/
theorem projected_invalidProgramIndices (ε : ℕ → ℕ) :
    LambdaTree.Projected ε {x | ¬ ValidProgramIndex ε (x 0)} := by
  have ht := LambdaTree.UniformProjected.const (LambdaTree.complemented_totalIndices ε).2
  have hb := LambdaTree.UniformProjected.const (projected_badComputationTables ε)
  obtain ⟨T,_,hT⟩ := ht.union hb
  have h := (show LambdaTree.Projected ε
      (({x | LambdaTree.TotalIndex ε (x 0)} : Set (ℕ → ℕ))ᶜ ∪
        {x | ∃ q, ComputationTable ε (x 0) q ∧ ¬ (streamLabels (leftBaire q)).Valid})
      from ⟨T 0,hT 0⟩)
  convert h using 1
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff,not_validProgramIndex_iff]

/-- Total numerical programs may still fail the syntax at the root. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For an index intended to compute Borel-expression labels, totality is a separate requirement from the
    local syntax conditions and the absence of infinite branches. The corollary handles this requirement;
    it does not identify the total indices with the valid Borel-expression indices.
-/
theorem exists_total_invalid_program (ε : ℕ → ℕ) :
    ∃ e, LambdaTree.TotalIndex ε e ∧ ¬ ValidProgramIndex ε e := by
  obtain ⟨e, he⟩ := Term.closedProgram_surjective (constantProgram 0) (constantProgram_closed 0)
  refine ⟨e, ?_, ?_⟩
  · intro n
    refine ⟨0, ?_⟩
    rw [he]
    exact constantProgram_runs 0 ε n
  · rintro ⟨c, hc, hvalid⟩
    have hr := hc.2 []
    rw [he] at hr
    have hz := hr.output_unique (constantProgram_runs 0 ε (NatListCode.encode []))
    exact hvalid.1 (by simpa [Encodable.encode] using hz)

end BorelExpression
end PolishSpaceBook
