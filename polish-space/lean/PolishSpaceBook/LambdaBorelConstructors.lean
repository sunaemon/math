module

public import PolishSpaceBook.BorelExpressionCompleteness
public import PolishSpaceBook.LambdaCountableOperations

@[expose] public section

/-! # Lambda programs for basic, complement, and union expressions

The union constructor requires one joint label program for the entire family.
All programs retain the original input parameter. They compute finite labels,
not the truth of an arbitrary Borel expression at a point.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace BorelExpression
open LambdaRelative
local instance constructorListEncoding : Encodable (List ℕ) := NatListCode.encodable

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The three closed programs are
    $$\begin{aligned}
    B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
    V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
     (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
    C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
     (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
    \end{aligned}$$
    For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
    For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
    numerical inputs at the fixed parameter.
-/
def basicLabelTerm (n : ℕ) : AlphaTerm := numericalIfLe numericalIdentity
  (numericalConstant 0) (numericalConstant (n+3)) (numericalConstant 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Comparison with zero proves the assertion for $B_n$. For $V_P$ and $C_P$, first reduce the application of $P$
    and form the numerical pair; totality permits this even at the root and at absent children.
    At word code zero, the selectors then return one and two, respectively, independently of that
    auxiliary label. At a nonempty word code, predecessor and numerical projection recover exactly
    $i$ and $\LambdaListCode{s}$. The selector $R_1$ returns $c_i(s)$. The selector $D$ returns $c(s)$
    when $i=0$ and zero otherwise. These are precisely the defining label equations.
    All numerical subterms terminate by their beta-reduction theorems; the application of $P$ uses its
    finite beta/query derivation at the unchanged parameter. Composition and numerical output pairing
    combine these derivations into a derivation for each displayed program.
-/
theorem basicLabelTerm_computes (n : ℕ) : NumericalComputes (basicLabelTerm n)
    (fun w => basic n (NatListCode.decode w)) := by
  have h := numericalIdentity_computes.ifLe (numericalConstant_computes 0)
    (numericalConstant_computes (n+3)) (numericalConstant_computes 0)
  refine ⟨h.1,fun w => ?_⟩
  cases w with
  | zero => simpa [basicLabelTerm,basic,NatListCode.decode] using h.2 0
  | succ w => simpa [basicLabelTerm,basic,NatListCode.decode] using h.2 (w+1)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a numeral label $\ell$, define the closed selector
    $$R_\ell:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{\ell}}{\LambdaNumericProjection{2}z}}.$$
    It returns $\ell$ when the first component is zero and otherwise returns the second component.
    For complement labels use
    $$\begin{aligned}
    T&:=\lambdaab{z}{\LambdaNumericProjection{1}(\LambdaPred(\LambdaNumericProjection{1}z))},\\
    H&:=\lambdaab{z}{\LambdaLeCase{Tz}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{2}z}{\ChurchNumeral{0}}},\\
    D&:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{2}}{Hz}}.
    \end{aligned}$$
    Here and below, every displayed abbreviation is expanded before abstraction and all bound variables
    are chosen fresh. The selectors use the numerical comparison and branching term already constructed.
-/
def rootLabelSelector (label : ℕ) : AlphaTerm := numericalIfLe
  (numericalProjectionTerm true) (numericalConstant 0)
  (numericalConstant label) (numericalProjectionTerm false)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Comparison with zero proves the assertion for $B_n$. For $V_P$ and $C_P$, first reduce the application of $P$
    and form the numerical pair; totality permits this even at the root and at absent children.
    At word code zero, the selectors then return one and two, respectively, independently of that
    auxiliary label. At a nonempty word code, predecessor and numerical projection recover exactly
    $i$ and $\LambdaListCode{s}$. The selector $R_1$ returns $c_i(s)$. The selector $D$ returns $c(s)$
    when $i=0$ and zero otherwise. These are precisely the defining label equations.
    All numerical subterms terminate by their beta-reduction theorems; the application of $P$ uses its
    finite beta/query derivation at the unchanged parameter. Composition and numerical output pairing
    combine these derivations into a derivation for each displayed program.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a numeral label $\ell$, define the closed selector
    $$R_\ell:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{\ell}}{\LambdaNumericProjection{2}z}}.$$
    It returns $\ell$ when the first component is zero and otherwise returns the second component.
    For complement labels use
    $$\begin{aligned}
    T&:=\lambdaab{z}{\LambdaNumericProjection{1}(\LambdaPred(\LambdaNumericProjection{1}z))},\\
    H&:=\lambdaab{z}{\LambdaLeCase{Tz}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{2}z}{\ChurchNumeral{0}}},\\
    D&:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{2}}{Hz}}.
    \end{aligned}$$
    Here and below, every displayed abbreviation is expanded before abstraction and all bound variables
    are chosen fresh. The selectors use the numerical comparison and branching term already constructed.
-/
theorem rootLabelSelector_computes (label : ℕ) : NumericalComputes (rootLabelSelector label)
    (fun z => if z.unpair.1 = 0 then label else z.unpair.2) := by
  simpa [rootLabelSelector] using (projection_computes true).ifLe (numericalConstant_computes 0)
    (numericalConstant_computes label) (projection_computes false)

/-- A nonempty list code is one plus the pair of its head and tail code. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use the label operations of §{sec:edst-borel-constructors}. A label program takes an oracle argument $o$
    and a numerical word code $w$. The empty word has code zero, and
    $$\LambdaListCode{(i)\concat s}=\NatPair{i}{\LambdaListCode{s}}+1.$$
    Thus on a nonempty word, $\LambdaPred w$ returns the pair of the first entry and the remaining word code.
    At code zero the same term returns zero, so all the auxiliary computations below remain defined.
-/
def constructorNodePartsTerm : AlphaTerm := predecessorTerm

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use the label operations of §{sec:edst-borel-constructors}. A label program takes an oracle argument $o$
    and a numerical word code $w$. The empty word has code zero, and
    $$\LambdaListCode{(i)\concat s}=\NatPair{i}{\LambdaListCode{s}}+1.$$
    Thus on a nonempty word, $\LambdaPred w$ returns the pair of the first entry and the remaining word code.
    At code zero the same term returns zero, so all the auxiliary computations below remain defined.
-/
theorem constructorNodeParts_computes : NumericalComputes constructorNodePartsTerm (fun w => w-1) :=
  predecessor_computes

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The three closed programs are
    $$\begin{aligned}
    B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
    V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
     (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
    C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
     (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
    \end{aligned}$$
    For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
    For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
    numerical inputs at the fixed parameter.
-/
def unionLabelProgram (P : AlphaTerm) : AlphaTerm := mapOutputProgram (rootLabelSelector 1)
  (pairOutputProgram (liftNumericalProgram numericalIdentity) (reindexProgram P constructorNodePartsTerm))

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Computable Borel-expression constructors
  excerpt: |
    Fix $\varepsilon$. A leaf has a computable label map. If a closed lambda program computes the labels of
    $c$ relative to $\varepsilon$, then another such program computes the labels of $\BorelComplementCode{c}$.
    If one closed program computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$ for all $i,s$, then another
    computes the labels of $\BorelUnionCode{(c_i)}$ at the same parameter.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Borel-label constructor programs}{Borel-label constructor programs}]
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Test whether the input word is empty. Otherwise decode its first entry and remaining word. The leaf
    returns zero on nonempty words; the complement retains only first entry zero; the union supplies the
    first entry and remaining word to the given joint program. The list encoding, numerical projections,
    and branching terms implement these operations. The explicit closed terms and their beta/query
    reductions are given in §{sec:lambda-borel-constructor-programs}. They compute labels on every word,
    including absent nodes. No test of expression validity or evaluation of Borel membership is used.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The three closed programs are
    $$\begin{aligned}
    B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
    V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
     (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
    C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
     (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
    \end{aligned}$$
    For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
    For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
    numerical inputs at the fixed parameter.
-/
theorem unionLabelProgram_computes {ε : ℕ → ℕ} {P : AlphaTerm} (c : ℕ → BorelExpression)
    (hP : Computes ε P (fun z : ℕ => c z.unpair.1 (NatListCode.decode z.unpair.2))) :
    Computes ε (unionLabelProgram P) (union c) := by
  have h := ((ofNumerical numericalIdentity_computes ε).pair
    (hP.reindex constructorNodeParts_computes)).map (rootLabelSelector_computes 1)
  refine ⟨h.1,fun s => ?_⟩
  cases s with
  | nil => simpa [Encodable.encode,NatListCode.encode,NatListCode.decode,union,complement,graft,absent,unionLabelProgram] using h.2 0
  | cons i s =>
      simpa [Encodable.encode,NatListCode.encode,NatListCode.decode,union,complement,graft,absent,unionLabelProgram]
        using h.2 (NatListCode.encode (i :: s))

theorem labelCodes_computes {ε : ℕ → ℕ} {P : AlphaTerm} {c : BorelExpression}
    (hP : Computes ε P c) : Computes ε P (fun w : ℕ => c (NatListCode.decode w)) :=
  ⟨hP.1,fun w => by simpa [Encodable.encode] using hP.2 (NatListCode.decode w)⟩

/-- Input (word-code,subexpression-label); only child zero is retained. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a numeral label $\ell$, define the closed selector
    $$R_\ell:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{\ell}}{\LambdaNumericProjection{2}z}}.$$
    It returns $\ell$ when the first component is zero and otherwise returns the second component.
    For complement labels use
    $$\begin{aligned}
    T&:=\lambdaab{z}{\LambdaNumericProjection{1}(\LambdaPred(\LambdaNumericProjection{1}z))},\\
    H&:=\lambdaab{z}{\LambdaLeCase{Tz}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{2}z}{\ChurchNumeral{0}}},\\
    D&:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{2}}{Hz}}.
    \end{aligned}$$
    Here and below, every displayed abbreviation is expanded before abstraction and all bound variables
    are chosen fresh. The selectors use the numerical comparison and branching term already constructed.
-/
def complementLabelSelector : AlphaTerm := numericalIfLe
  (numericalProjectionTerm true) (numericalConstant 0) (numericalConstant 2)
  (numericalIfLe
    (numericalCompose (numericalProjectionTerm true)
      (numericalCompose predecessorTerm (numericalProjectionTerm true)))
    (numericalConstant 0) (numericalProjectionTerm false) (numericalConstant 0))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Comparison with zero proves the assertion for $B_n$. For $V_P$ and $C_P$, first reduce the application of $P$
    and form the numerical pair; totality permits this even at the root and at absent children.
    At word code zero, the selectors then return one and two, respectively, independently of that
    auxiliary label. At a nonempty word code, predecessor and numerical projection recover exactly
    $i$ and $\LambdaListCode{s}$. The selector $R_1$ returns $c_i(s)$. The selector $D$ returns $c(s)$
    when $i=0$ and zero otherwise. These are precisely the defining label equations.
    All numerical subterms terminate by their beta-reduction theorems; the application of $P$ uses its
    finite beta/query derivation at the unchanged parameter. Composition and numerical output pairing
    combine these derivations into a derivation for each displayed program.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a numeral label $\ell$, define the closed selector
    $$R_\ell:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{\ell}}{\LambdaNumericProjection{2}z}}.$$
    It returns $\ell$ when the first component is zero and otherwise returns the second component.
    For complement labels use
    $$\begin{aligned}
    T&:=\lambdaab{z}{\LambdaNumericProjection{1}(\LambdaPred(\LambdaNumericProjection{1}z))},\\
    H&:=\lambdaab{z}{\LambdaLeCase{Tz}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{2}z}{\ChurchNumeral{0}}},\\
    D&:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
     {\ChurchNumeral{2}}{Hz}}.
    \end{aligned}$$
    Here and below, every displayed abbreviation is expanded before abstraction and all bound variables
    are chosen fresh. The selectors use the numerical comparison and branching term already constructed.
-/
theorem complementLabelSelector_computes : NumericalComputes complementLabelSelector
    (fun z => if z.unpair.1 = 0 then 2
      else if (z.unpair.1-1).unpair.1 = 0 then z.unpair.2 else 0) := by
  simpa [complementLabelSelector] using (projection_computes true).ifLe (numericalConstant_computes 0)
    (numericalConstant_computes 2)
    (((projection_computes true).comp (predecessor_computes.comp (projection_computes true))).ifLe
      (numericalConstant_computes 0) (projection_computes false) (numericalConstant_computes 0))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The three closed programs are
    $$\begin{aligned}
    B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
    V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
     (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
    C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
     (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
    \end{aligned}$$
    For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
    For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
    numerical inputs at the fixed parameter.
-/
def complementLabelProgram (P : AlphaTerm) : AlphaTerm := mapOutputProgram complementLabelSelector
  (pairOutputProgram (liftNumericalProgram numericalIdentity)
    (reindexProgram P (numericalCompose (numericalProjectionTerm false) predecessorTerm)))

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Computable Borel-expression constructors
  excerpt: |
    Fix $\varepsilon$. A leaf has a computable label map. If a closed lambda program computes the labels of
    $c$ relative to $\varepsilon$, then another such program computes the labels of $\BorelComplementCode{c}$.
    If one closed program computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$ for all $i,s$, then another
    computes the labels of $\BorelUnionCode{(c_i)}$ at the same parameter.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Borel-label constructor programs}{Borel-label constructor programs}]
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The three closed programs are
    $$\begin{aligned}
    B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
    V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
     (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
    C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
     (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
    \end{aligned}$$
    For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
    For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
    numerical inputs at the fixed parameter.
-/
theorem complementLabelProgram_computes {ε : ℕ → ℕ} {P : AlphaTerm} {c : BorelExpression}
    (hP : Computes ε P c) : Computes ε (complementLabelProgram P) (complement c) := by
  have h := ((ofNumerical numericalIdentity_computes ε).pair
    ((labelCodes_computes hP).reindex ((projection_computes false).comp predecessor_computes))).map
      complementLabelSelector_computes
  refine ⟨h.1,fun s => ?_⟩
  cases s with
  | nil => simpa [Encodable.encode,NatListCode.encode,NatListCode.decode,union,complement,graft,absent,unionLabelProgram,complementLabelProgram] using h.2 0
  | cons i s =>
      by_cases hi : i = 0 <;>
        simpa [hi,Encodable.encode,complement,graft,absent] using (show OracleRuns ε (complementLabelProgram P)
          (NatListCode.encode (i :: s)) (if i = 0 then c s else 0) from by
          simpa [Encodable.encode,NatListCode.encode,NatListCode.decode,union,complement,graft,absent,unionLabelProgram,complementLabelProgram]
        using h.2 (NatListCode.encode (i :: s)))

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Computable Borel-expression constructors
  excerpt: |
    Fix $\varepsilon$. A leaf has a computable label map. If a closed lambda program computes the labels of
    $c$ relative to $\varepsilon$, then another such program computes the labels of $\BorelComplementCode{c}$.
    If one closed program computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$ for all $i,s$, then another
    computes the labels of $\BorelUnionCode{(c_i)}$ at the same parameter.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Borel-label constructor programs}{Borel-label constructor programs}]
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The three closed programs are
    $$\begin{aligned}
    B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
    V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
     (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
    C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
     (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
    \end{aligned}$$
    For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
    For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
    numerical inputs at the fixed parameter.
-/
theorem basicLabelProgram_computes (ε : ℕ → ℕ) (n : ℕ) :
    Computes ε (liftNumericalProgram (basicLabelTerm n)) (basic n) := by
  have h := ofNumerical (basicLabelTerm_computes n) ε
  exact ⟨h.1,fun s => by simpa [Encodable.encode] using h.2 (NatListCode.encode s)⟩

end BorelExpression
end PolishSpaceBook
