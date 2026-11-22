module

public import PolishSpaceBook.BorelRankLabelStates
public import PolishSpaceBook.LambdaRelativeIteration
public import PolishSpaceBook.LambdaRelativeProducts
public import PolishSpaceBook.LambdaListPrefixes

@[expose] public section

/-! # Closed lambda terms for one rank-label update

The selector receives the state together with two numerical answers from the
supplied edge-label and bound-relation programs. Both programs are total at the
fixed parameter, so even unused auxiliary calls terminate.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace RankBound
open LambdaRelative
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For readability, in the following term bodies write $p_i:=\LambdaNumericProjection{i}$ and
    $\langle X,Y\rangle_\lambda:=\LambdaNumericPair\,X\,Y$.
    These abbreviations denote numerical lambda terms, not semantic pairing of their values.
    Define
    $$\begin{aligned}
    A(z)&:=p_1(p_2z),&S(z)&:=p_1(p_2(p_2z)),\\
    W(z)&:=p_2(p_2(p_2z)),&T(z)&:=\LambdaListDrop\,(W(z))\,\ChurchNumeral{5},\\
    H_i(z)&:=\LambdaListGet\,\langle W(z),\ChurchNumeral{i}\rangle_\lambda.
    \end{aligned}$$
    Missing list entries are read as zero. The edge and relation input bodies are
    $$U(z):=\langle H_1(z),\langle S(z),T(z)\rangle_\lambda\rangle_\lambda,
    \qquad V(z):=\langle H_4(z),A(z)\rangle_\lambda.$$
-/
def boundFieldTerm : AlphaTerm :=
  (numericalCompose
     (numericalProjectionTerm true)
     (numericalCompose (numericalProjectionTerm false) numericalIdentity))

def boundFieldValue (z : ℕ) : ℕ :=
  z.unpair.2.unpair.1

theorem boundField_computes : NumericalComputes boundFieldTerm boundFieldValue := by
  have h :=
    ((projection_computes true).comp ((projection_computes false).comp numericalIdentity_computes))
  refine ⟨h.1, fun z => ?_⟩
  simpa [boundFieldTerm,boundFieldValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For readability, in the following term bodies write $p_i:=\LambdaNumericProjection{i}$ and
    $\langle X,Y\rangle_\lambda:=\LambdaNumericPair\,X\,Y$.
    These abbreviations denote numerical lambda terms, not semantic pairing of their values.
    Define
    $$\begin{aligned}
    A(z)&:=p_1(p_2z),&S(z)&:=p_1(p_2(p_2z)),\\
    W(z)&:=p_2(p_2(p_2z)),&T(z)&:=\LambdaListDrop\,(W(z))\,\ChurchNumeral{5},\\
    H_i(z)&:=\LambdaListGet\,\langle W(z),\ChurchNumeral{i}\rangle_\lambda.
    \end{aligned}$$
    Missing list entries are read as zero. The edge and relation input bodies are
    $$U(z):=\langle H_1(z),\langle S(z),T(z)\rangle_\lambda\rangle_\lambda,
    \qquad V(z):=\langle H_4(z),A(z)\rangle_\lambda.$$
-/
def nodeFieldTerm : AlphaTerm :=
  (numericalCompose
     (numericalProjectionTerm true)
     (numericalCompose
        (numericalProjectionTerm false)
        (numericalCompose (numericalProjectionTerm false) numericalIdentity)))

def nodeFieldValue (z : ℕ) : ℕ :=
  z.unpair.2.unpair.2.unpair.1

theorem nodeField_computes : NumericalComputes nodeFieldTerm nodeFieldValue := by
  have h :=
    ((projection_computes true).comp
       ((projection_computes false).comp ((projection_computes false).comp numericalIdentity_computes)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [nodeFieldTerm,nodeFieldValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For readability, in the following term bodies write $p_i:=\LambdaNumericProjection{i}$ and
    $\langle X,Y\rangle_\lambda:=\LambdaNumericPair\,X\,Y$.
    These abbreviations denote numerical lambda terms, not semantic pairing of their values.
    Define
    $$\begin{aligned}
    A(z)&:=p_1(p_2z),&S(z)&:=p_1(p_2(p_2z)),\\
    W(z)&:=p_2(p_2(p_2z)),&T(z)&:=\LambdaListDrop\,(W(z))\,\ChurchNumeral{5},\\
    H_i(z)&:=\LambdaListGet\,\langle W(z),\ChurchNumeral{i}\rangle_\lambda.
    \end{aligned}$$
    Missing list entries are read as zero. The edge and relation input bodies are
    $$U(z):=\langle H_1(z),\langle S(z),T(z)\rangle_\lambda\rangle_\lambda,
    \qquad V(z):=\langle H_4(z),A(z)\rangle_\lambda.$$
-/
def wordFieldTerm : AlphaTerm :=
  (numericalCompose
     (numericalProjectionTerm false)
     (numericalCompose
        (numericalProjectionTerm false)
        (numericalCompose (numericalProjectionTerm false) numericalIdentity)))

def wordFieldValue (z : ℕ) : ℕ :=
  z.unpair.2.unpair.2.unpair.2

theorem wordField_computes : NumericalComputes wordFieldTerm wordFieldValue := by
  have h :=
    ((projection_computes false).comp
       ((projection_computes false).comp ((projection_computes false).comp numericalIdentity_computes)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordFieldTerm,wordFieldValue] using h.2 z

def wordEntry0Term : AlphaTerm :=
  (numericalCompose listGetTerm (pairNumerical wordFieldTerm (numericalConstant 0)))

def wordEntry0Value (z : ℕ) : ℕ :=
  (NatListCode.decode (wordFieldValue z)).getD 0 0

theorem wordEntry0_computes : NumericalComputes wordEntry0Term wordEntry0Value := by
  have h := (listGet_computes.comp (wordField_computes.pair (numericalConstant_computes 0)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordEntry0Term,wordEntry0Value] using h.2 z

def wordEntry1Term : AlphaTerm :=
  (numericalCompose listGetTerm (pairNumerical wordFieldTerm (numericalConstant 1)))

def wordEntry1Value (z : ℕ) : ℕ :=
  (NatListCode.decode (wordFieldValue z)).getD 1 0

theorem wordEntry1_computes : NumericalComputes wordEntry1Term wordEntry1Value := by
  have h := (listGet_computes.comp (wordField_computes.pair (numericalConstant_computes 1)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordEntry1Term,wordEntry1Value] using h.2 z

def wordEntry2Term : AlphaTerm :=
  (numericalCompose listGetTerm (pairNumerical wordFieldTerm (numericalConstant 2)))

def wordEntry2Value (z : ℕ) : ℕ :=
  (NatListCode.decode (wordFieldValue z)).getD 2 0

theorem wordEntry2_computes : NumericalComputes wordEntry2Term wordEntry2Value := by
  have h := (listGet_computes.comp (wordField_computes.pair (numericalConstant_computes 2)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordEntry2Term,wordEntry2Value] using h.2 z

def wordEntry3Term : AlphaTerm :=
  (numericalCompose listGetTerm (pairNumerical wordFieldTerm (numericalConstant 3)))

def wordEntry3Value (z : ℕ) : ℕ :=
  (NatListCode.decode (wordFieldValue z)).getD 3 0

theorem wordEntry3_computes : NumericalComputes wordEntry3Term wordEntry3Value := by
  have h := (listGet_computes.comp (wordField_computes.pair (numericalConstant_computes 3)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordEntry3Term,wordEntry3Value] using h.2 z

def wordEntry4Term : AlphaTerm :=
  (numericalCompose listGetTerm (pairNumerical wordFieldTerm (numericalConstant 4)))

def wordEntry4Value (z : ℕ) : ℕ :=
  (NatListCode.decode (wordFieldValue z)).getD 4 0

theorem wordEntry4_computes : NumericalComputes wordEntry4Term wordEntry4Value := by
  have h := (listGet_computes.comp (wordField_computes.pair (numericalConstant_computes 4)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordEntry4Term,wordEntry4Value] using h.2 z

def wordTailTerm : AlphaTerm :=
  (numericalCompose (uncurryNumerical listDropTerm) (pairNumerical wordFieldTerm (numericalConstant 5)))

def wordTailValue (z : ℕ) : ℕ :=
  NatListCode.encode ((NatListCode.decode (wordFieldValue z)).drop 5)

theorem wordTail_computes : NumericalComputes wordTailTerm wordTailValue := by
  have h :=
    ((uncurryNumerical_computes listDropTerm_closed (fun e n => NatListCode.encode ((NatListCode.decode e).drop n)) listDropTerm_apply).comp
       (wordField_computes.pair (numericalConstant_computes 5)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [wordTailTerm,wordTailValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For readability, in the following term bodies write $p_i:=\LambdaNumericProjection{i}$ and
    $\langle X,Y\rangle_\lambda:=\LambdaNumericPair\,X\,Y$.
    These abbreviations denote numerical lambda terms, not semantic pairing of their values.
    Define
    $$\begin{aligned}
    A(z)&:=p_1(p_2z),&S(z)&:=p_1(p_2(p_2z)),\\
    W(z)&:=p_2(p_2(p_2z)),&T(z)&:=\LambdaListDrop\,(W(z))\,\ChurchNumeral{5},\\
    H_i(z)&:=\LambdaListGet\,\langle W(z),\ChurchNumeral{i}\rangle_\lambda.
    \end{aligned}$$
    Missing list entries are read as zero. The edge and relation input bodies are
    $$U(z):=\langle H_1(z),\langle S(z),T(z)\rangle_\lambda\rangle_\lambda,
    \qquad V(z):=\langle H_4(z),A(z)\rangle_\lambda.$$
-/
def edgeInputTerm : AlphaTerm :=
  (pairNumerical wordEntry1Term (pairNumerical nodeFieldTerm wordTailTerm))

def edgeInputValue (z : ℕ) : ℕ :=
  Nat.pair (wordEntry1Value z) (Nat.pair (nodeFieldValue z) (wordTailValue z))

theorem edgeInput_computes : NumericalComputes edgeInputTerm edgeInputValue := by
  have h := (wordEntry1_computes.pair (nodeField_computes.pair wordTail_computes))
  refine ⟨h.1, fun z => ?_⟩
  simpa [edgeInputTerm,edgeInputValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For readability, in the following term bodies write $p_i:=\LambdaNumericProjection{i}$ and
    $\langle X,Y\rangle_\lambda:=\LambdaNumericPair\,X\,Y$.
    These abbreviations denote numerical lambda terms, not semantic pairing of their values.
    Define
    $$\begin{aligned}
    A(z)&:=p_1(p_2z),&S(z)&:=p_1(p_2(p_2z)),\\
    W(z)&:=p_2(p_2(p_2z)),&T(z)&:=\LambdaListDrop\,(W(z))\,\ChurchNumeral{5},\\
    H_i(z)&:=\LambdaListGet\,\langle W(z),\ChurchNumeral{i}\rangle_\lambda.
    \end{aligned}$$
    Missing list entries are read as zero. The edge and relation input bodies are
    $$U(z):=\langle H_1(z),\langle S(z),T(z)\rangle_\lambda\rangle_\lambda,
    \qquad V(z):=\langle H_4(z),A(z)\rangle_\lambda.$$
-/
def relationInputTerm : AlphaTerm :=
  (pairNumerical wordEntry4Term boundFieldTerm)

def relationInputValue (z : ℕ) : ℕ :=
  Nat.pair (wordEntry4Value z) (boundFieldValue z)

theorem relationInput_computes : NumericalComputes relationInputTerm relationInputValue := by
  have h := (wordEntry4_computes.pair boundField_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [relationInputTerm,relationInputValue] using h.2 z

def initialRankStateTerm : AlphaTerm :=
  (pairNumerical (numericalConstant 1) numericalIdentity)

def initialRankStateValue (z : ℕ) : ℕ :=
  Nat.pair 1 z

theorem initialRankState_computes : NumericalComputes initialRankStateTerm initialRankStateValue := by
  have h := ((numericalConstant_computes 1).pair numericalIdentity_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [initialRankStateTerm,initialRankStateValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The update program and the initial input to the iterator are
    $$\begin{aligned}
    \Delta_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{
     Z\langle z,\langle Po(U(z)),Qo(V(z))\rangle_\lambda\rangle_\lambda}},\\
    I&:=\lambdaab{x}{\langle\langle\ChurchNumeral{1},x\rangle_\lambda,
     \LambdaSucc(\LambdaListLength(p_2(p_2x)))\rangle_\lambda}.
    \end{aligned}$$
    \begin{mathmeta}
      \define{LambdaRankLabelProgram}
    \end{mathmeta}
    The required closed program is
    $$\LambdaRankLabelProgram{P}{Q}:=\lambdaab{o}{\lambdaab{x}{
     p_2(\LambdaIterateProgram{\Delta_{P,Q}}\,o\,(Ix))}}.$$
    Its input is $\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}$.
-/
def rankIterationInputTerm : AlphaTerm :=
  (pairNumerical
     initialRankStateTerm
     (numericalCompose
        successorTerm
        (numericalCompose
           listLengthTerm
           (numericalCompose
              (numericalProjectionTerm false)
              (numericalCompose (numericalProjectionTerm false) numericalIdentity)))))

def rankIterationInputValue (z : ℕ) : ℕ :=
  Nat.pair (initialRankStateValue z) ((NatListCode.decode z.unpair.2.unpair.2).length + 1)

theorem rankIterationInput_computes : NumericalComputes rankIterationInputTerm rankIterationInputValue := by
  have h :=
    (initialRankState_computes.pair
       (successor_computes.comp
          (listLength_computes.comp
             ((projection_computes false).comp
                ((projection_computes false).comp numericalIdentity_computes)))))
  refine ⟨h.1, fun z => ?_⟩
  simpa [rankIterationInputTerm,rankIterationInputValue] using h.2 z

def selectorStateTerm : AlphaTerm :=
  (numericalCompose (numericalProjectionTerm true) numericalIdentity)

def selectorStateValue (z : ℕ) : ℕ :=
  z.unpair.1

theorem selectorState_computes : NumericalComputes selectorStateTerm selectorStateValue := by
  have h := ((projection_computes true).comp numericalIdentity_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorStateTerm,selectorStateValue] using h.2 z

def selectorTagTerm : AlphaTerm :=
  (numericalCompose (numericalProjectionTerm true) selectorStateTerm)

def selectorTagValue (z : ℕ) : ℕ :=
  (selectorStateValue z).unpair.1

theorem selectorTag_computes : NumericalComputes selectorTagTerm selectorTagValue := by
  have h := ((projection_computes true).comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorTagTerm,selectorTagValue] using h.2 z

def selectorLengthTerm : AlphaTerm :=
  (numericalCompose listLengthTerm (numericalCompose wordFieldTerm selectorStateTerm))

def selectorLengthValue (z : ℕ) : ℕ :=
  (NatListCode.decode (wordFieldValue (selectorStateValue z))).length

theorem selectorLength_computes : NumericalComputes selectorLengthTerm selectorLengthValue := by
  have h := (listLength_computes.comp (wordField_computes.comp selectorState_computes))
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorLengthTerm,selectorLengthValue] using h.2 z

def selectorEntry0Term : AlphaTerm :=
  (numericalCompose wordEntry0Term selectorStateTerm)

def selectorEntry0Value (z : ℕ) : ℕ :=
  wordEntry0Value (selectorStateValue z)

theorem selectorEntry0_computes : NumericalComputes selectorEntry0Term selectorEntry0Value := by
  have h := (wordEntry0_computes.comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorEntry0Term,selectorEntry0Value] using h.2 z

def selectorEntry1Term : AlphaTerm :=
  (numericalCompose wordEntry1Term selectorStateTerm)

def selectorEntry1Value (z : ℕ) : ℕ :=
  wordEntry1Value (selectorStateValue z)

theorem selectorEntry1_computes : NumericalComputes selectorEntry1Term selectorEntry1Value := by
  have h := (wordEntry1_computes.comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorEntry1Term,selectorEntry1Value] using h.2 z

def selectorEntry2Term : AlphaTerm :=
  (numericalCompose wordEntry2Term selectorStateTerm)

def selectorEntry2Value (z : ℕ) : ℕ :=
  wordEntry2Value (selectorStateValue z)

theorem selectorEntry2_computes : NumericalComputes selectorEntry2Term selectorEntry2Value := by
  have h := (wordEntry2_computes.comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorEntry2Term,selectorEntry2Value] using h.2 z

def selectorEntry3Term : AlphaTerm :=
  (numericalCompose wordEntry3Term selectorStateTerm)

def selectorEntry3Value (z : ℕ) : ℕ :=
  wordEntry3Value (selectorStateValue z)

theorem selectorEntry3_computes : NumericalComputes selectorEntry3Term selectorEntry3Value := by
  have h := (wordEntry3_computes.comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorEntry3Term,selectorEntry3Value] using h.2 z

def selectorEntry4Term : AlphaTerm :=
  (numericalCompose wordEntry4Term selectorStateTerm)

def selectorEntry4Value (z : ℕ) : ℕ :=
  wordEntry4Value (selectorStateValue z)

theorem selectorEntry4_computes : NumericalComputes selectorEntry4Term selectorEntry4Value := by
  have h := (wordEntry4_computes.comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorEntry4Term,selectorEntry4Value] using h.2 z

def selectorTailTerm : AlphaTerm :=
  (numericalCompose wordTailTerm selectorStateTerm)

def selectorTailValue (z : ℕ) : ℕ :=
  wordTailValue (selectorStateValue z)

theorem selectorTail_computes : NumericalComputes selectorTailTerm selectorTailValue := by
  have h := (wordTail_computes.comp selectorState_computes)
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorTailTerm,selectorTailValue] using h.2 z

def selectorEdgeTerm : AlphaTerm :=
  (numericalCompose
     (numericalProjectionTerm true)
     (numericalCompose (numericalProjectionTerm false) numericalIdentity))

def selectorEdgeValue (z : ℕ) : ℕ :=
  z.unpair.2.unpair.1

theorem selectorEdge_computes : NumericalComputes selectorEdgeTerm selectorEdgeValue := by
  have h :=
    ((projection_computes true).comp ((projection_computes false).comp numericalIdentity_computes))
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorEdgeTerm,selectorEdgeValue] using h.2 z

def selectorRelationTerm : AlphaTerm :=
  (numericalCompose
     (numericalProjectionTerm false)
     (numericalCompose (numericalProjectionTerm false) numericalIdentity))

def selectorRelationValue (z : ℕ) : ℕ :=
  z.unpair.2.unpair.2

theorem selectorRelation_computes : NumericalComputes selectorRelationTerm selectorRelationValue := by
  have h :=
    ((projection_computes false).comp ((projection_computes false).comp numericalIdentity_computes))
  refine ⟨h.1, fun z => ?_⟩
  simpa [selectorRelationTerm,selectorRelationValue] using h.2 z

def nextRankStateTerm : AlphaTerm :=
  (pairNumerical
     (numericalConstant 1)
     (pairNumerical selectorEntry4Term (pairNumerical selectorEntry1Term selectorTailTerm)))

def nextRankStateValue (z : ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair (selectorEntry4Value z) (Nat.pair (selectorEntry1Value z) (selectorTailValue z)))

theorem nextRankState_computes : NumericalComputes nextRankStateTerm nextRankStateValue := by
  have h :=
    ((numericalConstant_computes 1).pair
       (selectorEntry4_computes.pair (selectorEntry1_computes.pair selectorTail_computes)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [nextRankStateTerm,nextRankStateValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical selector receives an augmented state $y$, consisting of the old state and the two answers.
    Within its body use
    $$\begin{aligned}
    z&:=p_1y,&\ell&:=\LambdaListLength\,(W(z)),&h_i&:=H_i(z),\\
    e&:=p_1(p_2y),&r&:=p_2(p_2y),&u&:=T(z).
    \end{aligned}$$
    Further abbreviate $D(X):=\langle\ChurchNumeral{0},X\rangle_\lambda$ and
    $C_k(X;Y,Z):=\LambdaLeCase{X}{\ChurchNumeral{k}}{Y}{Z}$.
    Set
    $$\begin{aligned}
    B&:=C_0(u;\ChurchNumeral{2},C_1(u;\ChurchNumeral{3},\ChurchNumeral{0})),\\
    N&:=\langle\ChurchNumeral{1},\langle h_4,\langle h_1,u\rangle_\lambda\rangle_\lambda\rangle_\lambda,\\
    J&:=C_0(h_4;D(e),D(\ChurchNumeral{0})),\\
    K&:=C_0(r;D(B),N),\\
    L&:=C_0(h_3;C_4(\ell;D(\ChurchNumeral{2}),J),C_4(\ell;D(\ChurchNumeral{1}),K)),\\
    M&:=C_0(h_2;C_3(\ell;D(\ChurchNumeral{1}),L),D(\ChurchNumeral{0})),\\
    F&:=C_1(\ell;D(\ChurchNumeral{1}),C_2(\ell;D(\ChurchNumeral{2}),M)),\\
    G&:=C_0(\ell;D(\ChurchNumeral{2}),C_0(h_0;F,D(\ChurchNumeral{0}))),\\
    Z&:=\lambdaab{y}{C_0(p_1z;z,G)}.
    \end{aligned}$$
    Expand all abbreviations before abstraction and choose fresh bound variables. In particular $Z$ is closed.
    The body $B$ gives the empty-expression label: the word codes zero and one represent the empty word
    and $(0)$, whose labels are two and three; every other word has label zero.
-/
def emptyTailLabelTerm : AlphaTerm :=
  (numericalIfLe
     selectorTailTerm
     (numericalConstant 0)
     (numericalConstant 2)
     (numericalIfLe selectorTailTerm (numericalConstant 1) (numericalConstant 3) (numericalConstant 0)))

def emptyTailLabelValue (z : ℕ) : ℕ :=
  if selectorTailValue z ≤ 0 then 2 else if selectorTailValue z ≤ 1 then 3 else 0

theorem emptyTailLabel_computes : NumericalComputes emptyTailLabelTerm emptyTailLabelValue := by
  have h :=
    (selectorTail_computes.ifLe
       (numericalConstant_computes 0)
       (numericalConstant_computes 2)
       (selectorTail_computes.ifLe
          (numericalConstant_computes 1)
          (numericalConstant_computes 3)
          (numericalConstant_computes 0)))
  refine ⟨h.1, fun z => ?_⟩
  simpa [emptyTailLabelTerm,emptyTailLabelValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical selector receives an augmented state $y$, consisting of the old state and the two answers.
    Within its body use
    $$\begin{aligned}
    z&:=p_1y,&\ell&:=\LambdaListLength\,(W(z)),&h_i&:=H_i(z),\\
    e&:=p_1(p_2y),&r&:=p_2(p_2y),&u&:=T(z).
    \end{aligned}$$
    Further abbreviate $D(X):=\langle\ChurchNumeral{0},X\rangle_\lambda$ and
    $C_k(X;Y,Z):=\LambdaLeCase{X}{\ChurchNumeral{k}}{Y}{Z}$.
    Set
    $$\begin{aligned}
    B&:=C_0(u;\ChurchNumeral{2},C_1(u;\ChurchNumeral{3},\ChurchNumeral{0})),\\
    N&:=\langle\ChurchNumeral{1},\langle h_4,\langle h_1,u\rangle_\lambda\rangle_\lambda\rangle_\lambda,\\
    J&:=C_0(h_4;D(e),D(\ChurchNumeral{0})),\\
    K&:=C_0(r;D(B),N),\\
    L&:=C_0(h_3;C_4(\ell;D(\ChurchNumeral{2}),J),C_4(\ell;D(\ChurchNumeral{1}),K)),\\
    M&:=C_0(h_2;C_3(\ell;D(\ChurchNumeral{1}),L),D(\ChurchNumeral{0})),\\
    F&:=C_1(\ell;D(\ChurchNumeral{1}),C_2(\ell;D(\ChurchNumeral{2}),M)),\\
    G&:=C_0(\ell;D(\ChurchNumeral{2}),C_0(h_0;F,D(\ChurchNumeral{0}))),\\
    Z&:=\lambdaab{y}{C_0(p_1z;z,G)}.
    \end{aligned}$$
    Expand all abbreviations before abstraction and choose fresh bound variables. In particular $Z$ is closed.
    The body $B$ gives the empty-expression label: the word codes zero and one represent the empty word
    and $(0)$, whose labels are two and three; every other word has label zero.
-/
def rankStepSelectorTerm : AlphaTerm :=
  (numericalIfLe
     selectorTagTerm
     (numericalConstant 0)
     selectorStateTerm
     (numericalIfLe
        selectorLengthTerm
        (numericalConstant 0)
        (pairNumerical (numericalConstant 0) (numericalConstant 2))
        (numericalIfLe
           selectorEntry0Term
           (numericalConstant 0)
           (numericalIfLe
              selectorLengthTerm
              (numericalConstant 1)
              (pairNumerical (numericalConstant 0) (numericalConstant 1))
              (numericalIfLe
                 selectorLengthTerm
                 (numericalConstant 2)
                 (pairNumerical (numericalConstant 0) (numericalConstant 2))
                 (numericalIfLe
                    selectorEntry2Term
                    (numericalConstant 0)
                    (numericalIfLe
                       selectorLengthTerm
                       (numericalConstant 3)
                       (pairNumerical (numericalConstant 0) (numericalConstant 1))
                       (numericalIfLe
                          selectorEntry3Term
                          (numericalConstant 0)
                          (numericalIfLe
                             selectorLengthTerm
                             (numericalConstant 4)
                             (pairNumerical (numericalConstant 0) (numericalConstant 2))
                             (numericalIfLe
                                selectorEntry4Term
                                (numericalConstant 0)
                                (pairNumerical (numericalConstant 0) selectorEdgeTerm)
                                (pairNumerical (numericalConstant 0) (numericalConstant 0))))
                          (numericalIfLe
                             selectorLengthTerm
                             (numericalConstant 4)
                             (pairNumerical (numericalConstant 0) (numericalConstant 1))
                             (numericalIfLe
                                selectorRelationTerm
                                (numericalConstant 0)
                                (pairNumerical (numericalConstant 0) emptyTailLabelTerm)
                                nextRankStateTerm))))
                    (pairNumerical (numericalConstant 0) (numericalConstant 0)))))
           (pairNumerical (numericalConstant 0) (numericalConstant 0)))))

def rankStepSelectorValue (z : ℕ) : ℕ :=
  if selectorTagValue z ≤ 0 then selectorStateValue z
  else if selectorLengthValue z ≤ 0 then Nat.pair 0 2
  else if selectorEntry0Value z ≤ 0 then
    if selectorLengthValue z ≤ 1 then Nat.pair 0 1
    else if selectorLengthValue z ≤ 2 then Nat.pair 0 2
    else if selectorEntry2Value z ≤ 0 then
      if selectorLengthValue z ≤ 3 then Nat.pair 0 1
      else if selectorEntry3Value z ≤ 0 then
        if selectorLengthValue z ≤ 4 then Nat.pair 0 2
        else if selectorEntry4Value z ≤ 0 then Nat.pair 0 (selectorEdgeValue z)
        else Nat.pair 0 0
      else if selectorLengthValue z ≤ 4 then Nat.pair 0 1
      else if selectorRelationValue z ≤ 0 then Nat.pair 0 (emptyTailLabelValue z)
      else nextRankStateValue z
    else Nat.pair 0 0
  else Nat.pair 0 0

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical selector receives an augmented state $y$, consisting of the old state and the two answers.
    Within its body use
    $$\begin{aligned}
    z&:=p_1y,&\ell&:=\LambdaListLength\,(W(z)),&h_i&:=H_i(z),\\
    e&:=p_1(p_2y),&r&:=p_2(p_2y),&u&:=T(z).
    \end{aligned}$$
    Further abbreviate $D(X):=\langle\ChurchNumeral{0},X\rangle_\lambda$ and
    $C_k(X;Y,Z):=\LambdaLeCase{X}{\ChurchNumeral{k}}{Y}{Z}$.
    Set
    $$\begin{aligned}
    B&:=C_0(u;\ChurchNumeral{2},C_1(u;\ChurchNumeral{3},\ChurchNumeral{0})),\\
    N&:=\langle\ChurchNumeral{1},\langle h_4,\langle h_1,u\rangle_\lambda\rangle_\lambda\rangle_\lambda,\\
    J&:=C_0(h_4;D(e),D(\ChurchNumeral{0})),\\
    K&:=C_0(r;D(B),N),\\
    L&:=C_0(h_3;C_4(\ell;D(\ChurchNumeral{2}),J),C_4(\ell;D(\ChurchNumeral{1}),K)),\\
    M&:=C_0(h_2;C_3(\ell;D(\ChurchNumeral{1}),L),D(\ChurchNumeral{0})),\\
    F&:=C_1(\ell;D(\ChurchNumeral{1}),C_2(\ell;D(\ChurchNumeral{2}),M)),\\
    G&:=C_0(\ell;D(\ChurchNumeral{2}),C_0(h_0;F,D(\ChurchNumeral{0}))),\\
    Z&:=\lambdaab{y}{C_0(p_1z;z,G)}.
    \end{aligned}$$
    Expand all abbreviations before abstraction and choose fresh bound variables. In particular $Z$ is closed.
    The body $B$ gives the empty-expression label: the word codes zero and one represent the empty word
    and $(0)$, whose labels are two and three; every other word has label zero.
-/
theorem rankStepSelector_computes : NumericalComputes rankStepSelectorTerm rankStepSelectorValue := by
  have h :=
    (selectorTag_computes.ifLe
       (numericalConstant_computes 0)
       selectorState_computes
       (selectorLength_computes.ifLe
          (numericalConstant_computes 0)
          ((numericalConstant_computes 0).pair (numericalConstant_computes 2))
          (selectorEntry0_computes.ifLe
             (numericalConstant_computes 0)
             (selectorLength_computes.ifLe
                (numericalConstant_computes 1)
                ((numericalConstant_computes 0).pair (numericalConstant_computes 1))
                (selectorLength_computes.ifLe
                   (numericalConstant_computes 2)
                   ((numericalConstant_computes 0).pair (numericalConstant_computes 2))
                   (selectorEntry2_computes.ifLe
                      (numericalConstant_computes 0)
                      (selectorLength_computes.ifLe
                         (numericalConstant_computes 3)
                         ((numericalConstant_computes 0).pair (numericalConstant_computes 1))
                         (selectorEntry3_computes.ifLe
                            (numericalConstant_computes 0)
                            (selectorLength_computes.ifLe
                               (numericalConstant_computes 4)
                               ((numericalConstant_computes 0).pair (numericalConstant_computes 2))
                               (selectorEntry4_computes.ifLe
                                  (numericalConstant_computes 0)
                                  ((numericalConstant_computes 0).pair selectorEdge_computes)
                                  ((numericalConstant_computes 0).pair (numericalConstant_computes 0))))
                            (selectorLength_computes.ifLe
                               (numericalConstant_computes 4)
                               ((numericalConstant_computes 0).pair (numericalConstant_computes 1))
                               (selectorRelation_computes.ifLe
                                  (numericalConstant_computes 0)
                                  ((numericalConstant_computes 0).pair emptyTailLabel_computes)
                                  nextRankState_computes))))
                      ((numericalConstant_computes 0).pair (numericalConstant_computes 0)))))
             ((numericalConstant_computes 0).pair (numericalConstant_computes 0)))))
  refine ⟨h.1, fun z => ?_⟩
  simpa [rankStepSelectorTerm,rankStepSelectorValue] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The update program and the initial input to the iterator are
    $$\begin{aligned}
    \Delta_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{
     Z\langle z,\langle Po(U(z)),Qo(V(z))\rangle_\lambda\rangle_\lambda}},\\
    I&:=\lambdaab{x}{\langle\langle\ChurchNumeral{1},x\rangle_\lambda,
     \LambdaSucc(\LambdaListLength(p_2(p_2x)))\rangle_\lambda}.
    \end{aligned}$$
    \begin{mathmeta}
      \define{LambdaRankLabelProgram}
    \end{mathmeta}
    The required closed program is
    $$\LambdaRankLabelProgram{P}{Q}:=\lambdaab{o}{\lambdaab{x}{
     p_2(\LambdaIterateProgram{\Delta_{P,Q}}\,o\,(Ix))}}.$$
    Its input is $\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}$.
-/
def rankStepProgram (P Q : AlphaTerm) : AlphaTerm :=
  mapOutputProgram rankStepSelectorTerm
    (pairOutputProgram (liftNumericalProgram numericalIdentity)
      (pairOutputProgram (reindexProgram P edgeInputTerm) (reindexProgram Q relationInputTerm)))

theorem rankStepProgram_computes_aux {ε : ℕ → ℕ} {P Q : AlphaTerm} {e r : ℕ → ℕ}
    (hP : Computes ε P e) (hQ : Computes ε Q r) :
    Computes ε (rankStepProgram P Q)
      (fun z : ℕ => rankStepSelectorValue (Nat.pair z
        (Nat.pair (e (edgeInputValue z)) (r (relationInputValue z))))) := by
  exact ((ofNumerical numericalIdentity_computes ε).pair
    ((hP.reindex edgeInput_computes).pair (hQ.reindex relationInput_computes))).map
      rankStepSelector_computes

end RankBound
end PolishSpaceBook
