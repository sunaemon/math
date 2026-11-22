module

public import PolishSpaceBook.LambdaCantorStageDecision
public import PolishSpaceBook.LambdaBorelConstructors
public import PolishSpaceBook.BorelExpressionBoolean

@[expose] public section

/-! # Borel labels for a binary tree body and its differences

Rejected finite words enumerate the open complement. The label program selects
a cylinder or an empty expression; Boolean constructors need no further jumps.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative BorelExpression
namespace CantorDerivative
attribute [local instance] Classical.propDecidable
local instance : Encodable (List ℕ) := NatListCode.encodable
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def binaryCylinderBasis (n : ℕ) : Set (ℕ → Bool) :=
  if Binary n then cyl (decodeWord n) else ∅

@[simp] theorem binaryCylinderBasis_zero : binaryCylinderBasis 0 = univ := by
  simp [binaryCylinderBasis,Binary,decodeWord,NatListCode.decode,cyl]

noncomputable def rejectedWordCode (T : Set (List Bool)) (n : ℕ) : Code :=
  if codedTree T n then Code.empty else Code.leaf n
noncomputable def outsideCode (T : Set (List Bool)) : Code := Code.iUnion (rejectedWordCode T)
noncomputable def bodyCode (T : Set (List Bool)) : Code := (outsideCode T).compl

@[simp] theorem value_rejectedWordCode (T : Set (List Bool)) (n : ℕ) :
    (rejectedWordCode T n).value binaryCylinderBasis =
      if codedTree T n then ∅ else binaryCylinderBasis n := by
  by_cases h : codedTree T n <;>
    simp [rejectedWordCode,h,Code.value_empty _ binaryCylinderBasis_zero,Code.value_leaf]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    For this construction interpret leaf $n$ as the cylinder $U_n$ of the binary word coded by $n$;
    if the decoded word is not binary, put $U_n=\emptyset$. In particular, $U_0=\CantorSpace$, since
    zero codes the empty word. Define
    $$\begin{aligned}
     e^T_n&:=\begin{cases}
     \BorelEmptyCode,&n\text{ codes a word in }T,\\
     \BorelLeafCode{n},&\text{otherwise},
     \end{cases}\\
     O_T&:=\BorelUnionCode{\Sequence{e^T_n}{n\in\omega}},\qquad
     C_T:=\BorelComplementCode{O_T},\\
     D_{T,S}&:=\BorelComplementCode{\BorelBinaryUnionCode{O_T}{C_S}}.
    \end{aligned}$$
    A point fails to belong to the body of a tree exactly when one of its finite prefixes is missing
    from the tree. Hence
    $$\BorelValue{O_T}=\SetDifference{\CantorSpace}{\TreeBody{T}},\qquad
     \BorelValue{C_T}=\TreeBody{T},\qquad
     \BorelValue{D_{T,S}}=\SetDifference{\TreeBody{T}}{\TreeBody{S}}.$$
    Nonbinary codes contribute empty leaves and do not change the union. The constructors ensure
    validity, even for an empty tree.
-/
theorem value_outsideCode (T : Set (List Bool)) :
    (outsideCode T).value binaryCylinderBasis = (treeBody T)ᶜ := by
  ext x
  simp only [outsideCode,Code.value_iUnion,mem_iUnion,value_rejectedWordCode]
  constructor
  · rintro ⟨n,hn⟩ hx
    by_cases ht : codedTree T n
    · simp [ht] at hn
    · simp only [ht,ite_false,binaryCylinderBasis] at hn
      split_ifs at hn with hb
      · apply ht
        exact ⟨hb,(seqPrefix_eq_of_mem_cyl hn) ▸ hx (decodeWord n).length⟩
      · exact hn
  · intro hx
    change ¬ (∀ k, seqPrefix x k ∈ T) at hx
    obtain ⟨k,hk⟩ := not_forall.mp hx
    let n := encodeWord (seqPrefix x k)
    have hn : ¬ codedTree T n := by simpa [codedTree,n,decodeWord_encodeWord,binary_encodeWord] using hk
    refine ⟨n,?_⟩
    simpa [hn,binaryCylinderBasis,n,binary_encodeWord,decodeWord_encodeWord] using mem_cyl_seqPrefix x k

theorem value_bodyCode (T : Set (List Bool)) :
    (bodyCode T).value binaryCylinderBasis = treeBody T := by
  rw [bodyCode,Code.value_compl,value_outsideCode,compl_compl]

/-- A leaf label, jointly in the leaf number and the address code. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $B_n,C_P,V_P$ from §{sec:lambda-borel-constructor-programs} and put $E:=C_{B_0}$, the label
    program for the empty expression. For numerical arguments abbreviate
    $$B(n,w):=\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\LambdaAdd\,n\,\ChurchNumeral{3}}{\ChurchNumeral{0}}.$$
    This jointly computes the label of leaf $n$ at address code $w$. Let $H$ be the pure numerical selector
    $$H:=\lambdaab{v}{\LambdaLeCase{\LambdaNumericProjection{1}v}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{1}(\LambdaNumericProjection{2}v)}
     {\LambdaNumericProjection{2}(\LambdaNumericProjection{2}v)}}.$$
    Thus on $\NatPair{c}{\NatPair{x}{y}}$ it returns $x$ when $c=0$, and $y$ otherwise.
-/
def jointLeafLabelTerm : AlphaTerm := numericalIfLe (numericalProjectionTerm false)
  (numericalConstant 0) (addNumerical (numericalProjectionTerm true) (numericalConstant 3))
  (numericalConstant 0)

theorem jointLeafLabelTerm_computes : NumericalComputes jointLeafLabelTerm
    (fun z : ℕ => (Code.leaf z.unpair.1).val (NatListCode.decode z.unpair.2)) := by
  have h := (projection_computes false).ifLe (numericalConstant_computes 0)
    ((projection_computes true).add (numericalConstant_computes 3)) (numericalConstant_computes 0)
  refine ⟨h.1,fun z => ?_⟩
  cases he : z.unpair.2 <;> simpa [jointLeafLabelTerm,Code.leaf,basic,NatListCode.decode,he] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $B_n,C_P,V_P$ from §{sec:lambda-borel-constructor-programs} and put $E:=C_{B_0}$, the label
    program for the empty expression. For numerical arguments abbreviate
    $$B(n,w):=\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\LambdaAdd\,n\,\ChurchNumeral{3}}{\ChurchNumeral{0}}.$$
    This jointly computes the label of leaf $n$ at address code $w$. Let $H$ be the pure numerical selector
    $$H:=\lambdaab{v}{\LambdaLeCase{\LambdaNumericProjection{1}v}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{1}(\LambdaNumericProjection{2}v)}
     {\LambdaNumericProjection{2}(\LambdaNumericProjection{2}v)}}.$$
    Thus on $\NatPair{c}{\NatPair{x}{y}}$ it returns $x$ when $c=0$, and $y$ otherwise.
-/
def emptyLabelProgram : AlphaTerm := complementLabelProgram (liftNumericalProgram (basicLabelTerm 0))

theorem emptyLabelProgram_computes (ε : ℕ → ℕ) : Computes ε emptyLabelProgram Code.empty.val :=
  complementLabelProgram_computes (basicLabelProgram_computes ε 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $B_n,C_P,V_P$ from §{sec:lambda-borel-constructor-programs} and put $E:=C_{B_0}$, the label
    program for the empty expression. For numerical arguments abbreviate
    $$B(n,w):=\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\LambdaAdd\,n\,\ChurchNumeral{3}}{\ChurchNumeral{0}}.$$
    This jointly computes the label of leaf $n$ at address code $w$. Let $H$ be the pure numerical selector
    $$H:=\lambdaab{v}{\LambdaLeCase{\LambdaNumericProjection{1}v}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{1}(\LambdaNumericProjection{2}v)}
     {\LambdaNumericProjection{2}(\LambdaNumericProjection{2}v)}}.$$
    Thus on $\NatPair{c}{\NatPair{x}{y}}$ it returns $x$ when $c=0$, and $y$ otherwise.
-/
def labelSelectorTerm : AlphaTerm := numericalIfLe (numericalProjectionTerm true)
  (numericalConstant 0)
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use $B_n,C_P,V_P$ from §{sec:lambda-borel-constructor-programs} and put $E:=C_{B_0}$, the label
    program for the empty expression. For numerical arguments abbreviate
    $$B(n,w):=\LambdaLeCase{w}{\ChurchNumeral{0}}
     {\LambdaAdd\,n\,\ChurchNumeral{3}}{\ChurchNumeral{0}}.$$
    This jointly computes the label of leaf $n$ at address code $w$. Let $H$ be the pure numerical selector
    $$H:=\lambdaab{v}{\LambdaLeCase{\LambdaNumericProjection{1}v}{\ChurchNumeral{0}}
     {\LambdaNumericProjection{1}(\LambdaNumericProjection{2}v)}
     {\LambdaNumericProjection{2}(\LambdaNumericProjection{2}v)}}.$$
    Thus on $\NatPair{c}{\NatPair{x}{y}}$ it returns $x$ when $c=0$, and $y$ otherwise.
-/
theorem labelSelectorTerm_computes : NumericalComputes labelSelectorTerm
    (fun z : ℕ => if z.unpair.1 = 0 then z.unpair.2.unpair.1 else z.unpair.2.unpair.2) := by
  simpa [labelSelectorTerm] using (projection_computes true).ifLe (numericalConstant_computes 0)
    ((projection_computes true).comp (projection_computes false))
    ((projection_computes false).comp (projection_computes false))

def selectLabelProgram (C X Y : AlphaTerm) : AlphaTerm :=
  mapOutputProgram labelSelectorTerm (pairOutputProgram C (pairOutputProgram X Y))

theorem selectLabelProgram_computes {ε : ℕ → ℕ} {C X Y : AlphaTerm} {c x y : ℕ → ℕ}
    (hc : Computes ε C c) (hx : Computes ε X x) (hy : Computes ε Y y) :
    Computes ε (selectLabelProgram C X Y) (fun z => if c z = 0 then x z else y z) := by
  simpa only [selectLabelProgram,Nat.unpair_pair] using (hc.pair (hx.pair hy)).map labelSelectorTerm_computes

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ be the tree decision programs. Decode $z=\NatPair{n}{w}$ by projections and define
    $$\begin{aligned}
     J_P&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,(Po\,n)\,
       (\LambdaNumericPair\,B(n,w)\,(Eo\,w)))}},\\
     O_P&:=V_{J_P},\qquad F_P:=C_{O_P},\\
     R_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,n\,
       (\LambdaNumericPair\,(O_Po\,w)\,(F_Qo\,w)))}},\\
     D_{P,Q}&:=C_{V_{R_{P,Q}}}.
    \end{aligned}$$
    Expand the projections and abbreviations with fresh binders. The resulting terms are closed and
    depend only on the supplied programs. They do not select a program separately for each tree or
    input parameter.
-/
def rejectedWordLabelProgram (P : AlphaTerm) : AlphaTerm :=
  selectLabelProgram (reindexProgram P (numericalProjectionTerm true))
    (liftNumericalProgram jointLeafLabelTerm)
    (reindexProgram emptyLabelProgram (numericalProjectionTerm false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ be the tree decision programs. Decode $z=\NatPair{n}{w}$ by projections and define
    $$\begin{aligned}
     J_P&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,(Po\,n)\,
       (\LambdaNumericPair\,B(n,w)\,(Eo\,w)))}},\\
     O_P&:=V_{J_P},\qquad F_P:=C_{O_P},\\
     R_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,n\,
       (\LambdaNumericPair\,(O_Po\,w)\,(F_Qo\,w)))}},\\
     D_{P,Q}&:=C_{V_{R_{P,Q}}}.
    \end{aligned}$$
    Expand the projections and abbreviations with fresh binders. The resulting terms are closed and
    depend only on the supplied programs. They do not select a program separately for each tree or
    input parameter.
-/
theorem rejectedWordLabelProgram_computes {ε : ℕ → ℕ} {P : AlphaTerm} {T : Set (List Bool)}
    (hP : Decides ε P (codedTree T)) :
    Computes ε (rejectedWordLabelProgram P)
      (fun z : ℕ => (rejectedWordCode T z.unpair.1).val (NatListCode.decode z.unpair.2)) := by
  have hl := ofNumerical jointLeafLabelTerm_computes ε
  have he := (labelCodes_computes (emptyLabelProgram_computes ε)).reindex (projection_computes false)
  have hc : Computes ε P (fun n : ℕ => if codedTree T n then 1 else 0) := ⟨hP.1,fun n => hP.runs n⟩
  have h := selectLabelProgram_computes (hc.reindex (projection_computes true)) hl he
  refine ⟨h.1,fun z => ?_⟩
  by_cases ht : codedTree T z.unpair.1 <;>
    simpa [rejectedWordLabelProgram,rejectedWordCode,ht] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ be the tree decision programs. Decode $z=\NatPair{n}{w}$ by projections and define
    $$\begin{aligned}
     J_P&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,(Po\,n)\,
       (\LambdaNumericPair\,B(n,w)\,(Eo\,w)))}},\\
     O_P&:=V_{J_P},\qquad F_P:=C_{O_P},\\
     R_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,n\,
       (\LambdaNumericPair\,(O_Po\,w)\,(F_Qo\,w)))}},\\
     D_{P,Q}&:=C_{V_{R_{P,Q}}}.
    \end{aligned}$$
    Expand the projections and abbreviations with fresh binders. The resulting terms are closed and
    depend only on the supplied programs. They do not select a program separately for each tree or
    input parameter.
-/
def outsideLabelProgram (P : AlphaTerm) : AlphaTerm := unionLabelProgram (rejectedWordLabelProgram P)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ be the tree decision programs. Decode $z=\NatPair{n}{w}$ by projections and define
    $$\begin{aligned}
     J_P&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,(Po\,n)\,
       (\LambdaNumericPair\,B(n,w)\,(Eo\,w)))}},\\
     O_P&:=V_{J_P},\qquad F_P:=C_{O_P},\\
     R_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,n\,
       (\LambdaNumericPair\,(O_Po\,w)\,(F_Qo\,w)))}},\\
     D_{P,Q}&:=C_{V_{R_{P,Q}}}.
    \end{aligned}$$
    Expand the projections and abbreviations with fresh binders. The resulting terms are closed and
    depend only on the supplied programs. They do not select a program separately for each tree or
    input parameter.
-/
def bodyLabelProgram (P : AlphaTerm) : AlphaTerm := complementLabelProgram (outsideLabelProgram P)

theorem outsideLabelProgram_computes {ε : ℕ → ℕ} {P : AlphaTerm} {T : Set (List Bool)}
    (hP : Decides ε P (codedTree T)) : Computes ε (outsideLabelProgram P) (outsideCode T).val :=
  unionLabelProgram_computes _ (rejectedWordLabelProgram_computes hP)

theorem bodyLabelProgram_computes {ε : ℕ → ℕ} {P : AlphaTerm} {T : Set (List Bool)}
    (hP : Decides ε P (codedTree T)) : Computes ε (bodyLabelProgram P) (bodyCode T).val :=
  complementLabelProgram_computes (outsideLabelProgram_computes hP)

noncomputable def differenceCode (T S : Set (List Bool)) : Code :=
  (Code.sup (outsideCode T) (bodyCode S)).compl

theorem value_differenceCode (T S : Set (List Bool)) :
    (differenceCode T S).value binaryCylinderBasis = treeBody T \ treeBody S := by
  rw [differenceCode,Code.value_compl,Code.value_sup,value_outsideCode,value_bodyCode]
  ext x
  simp only [mem_compl_iff,mem_union,mem_sdiff]
  tauto

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ be the tree decision programs. Decode $z=\NatPair{n}{w}$ by projections and define
    $$\begin{aligned}
     J_P&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,(Po\,n)\,
       (\LambdaNumericPair\,B(n,w)\,(Eo\,w)))}},\\
     O_P&:=V_{J_P},\qquad F_P:=C_{O_P},\\
     R_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,n\,
       (\LambdaNumericPair\,(O_Po\,w)\,(F_Qo\,w)))}},\\
     D_{P,Q}&:=C_{V_{R_{P,Q}}}.
    \end{aligned}$$
    Expand the projections and abbreviations with fresh binders. The resulting terms are closed and
    depend only on the supplied programs. They do not select a program separately for each tree or
    input parameter.
-/
def differenceLabelProgram (P Q : AlphaTerm) : AlphaTerm :=
  complementLabelProgram (unionLabelProgram
    (selectLabelProgram (liftNumericalProgram (numericalProjectionTerm true))
      (reindexProgram (outsideLabelProgram P) (numericalProjectionTerm false))
      (reindexProgram (bodyLabelProgram Q) (numericalProjectionTerm false))))

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Borel codes for tree differences
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    To compute a label of $e^T_n$, run the tree decider on $n$ and choose the corresponding empty or
    leaf label. This is one joint program in the leaf index and address. Apply the union and complement
    label programs of §{sec:edst-borel-constructors}. For the binary union, use the first expression at
    child zero and the second at every positive child. Each computation makes only finitely many
    calls to the supplied tree tests. §{sec:lambda-cantor-derivative-programs} displays the terms.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Tree Borel-label programs
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The numerical projections recover the leaf index and address. The tree decision and both candidate
    labels terminate; pairing their outputs and applying $H$ selects the empty label for an accepted
    word and the cylinder label for a rejected word. Thus $J_P$ computes the joint labels of the family
    $e^T_n$. The union and complement constructor equations give the assertions for $O_P,F_P$.
    In $R_{P,Q}$ the selector uses the child index: zero selects the first expression, and every positive
    index selects the second. A union followed by complementation gives the difference expression.
    All numerical steps are beta reductions, and every tree or label call retains the same input
    function. No evaluation of membership in an arbitrary Borel set is used.
    \end{proof}
-/
theorem differenceLabelProgram_computes {ε : ℕ → ℕ} {P Q : AlphaTerm} {T S : Set (List Bool)}
    (hP : Decides ε P (codedTree T)) (hQ : Decides ε Q (codedTree S)) :
    Computes ε (differenceLabelProgram P Q) (differenceCode T S).val := by
  have hx := (labelCodes_computes (outsideLabelProgram_computes hP)).reindex (projection_computes false)
  have hy := (labelCodes_computes (bodyLabelProgram_computes hQ)).reindex (projection_computes false)
  have hc := ofNumerical (projection_computes true) ε
  have hh := selectLabelProgram_computes hc hx hy
  have he : (fun z : ℕ => if z.unpair.1 = 0 then (outsideCode T).val (NatListCode.decode z.unpair.2)
      else (bodyCode S).val (NatListCode.decode z.unpair.2)) =
      (fun z : ℕ => (if z.unpair.1 = 0 then outsideCode T else bodyCode S).val (NatListCode.decode z.unpair.2)) := by
    funext z; split_ifs <;> rfl
  simp only [ite_true,Bool.false_eq_true,ite_false] at hh
  rw [he] at hh
  exact complementLabelProgram_computes (unionLabelProgram_computes _ hh)

def pureTreeProgram (P : AlphaTerm) : AlphaTerm :=
  liftNumericalProgram (app P (numericalConstant 0))

theorem pureTreeProgram_decides {P : AlphaTerm} {T : Set (List Bool)}
    (hP : Decides (fun _ => 0) P (codedTree T)) (ε : ℕ → ℕ) :
    Decides ε (pureTreeProgram P) (codedTree T) := by
  have hc : Computes (fun _ => 0) P (fun n : ℕ => if codedTree T n then 1 else 0) :=
    ⟨hP.1,fun n => hP.runs n⟩
  have h := ofNumerical (hc.toNumerical (numericalConstant_computes 0)) ε
  refine ⟨h.1,fun n => ⟨?_,?_⟩⟩ <;> intro hn
  · simpa only [pureTreeProgram,ite_eq_left hn,Encodable.encode_nat] using h.2 n
  · simpa only [pureTreeProgram,ite_eq_right hn,Encodable.encode_nat] using h.2 n


theorem bodyLabelProgram_closed {P : AlphaTerm} (hP : P.Closed) :
    (bodyLabelProgram P).Closed := by
  have htail : (numericalCompose (numericalProjectionTerm false) predecessorTerm).Closed :=
    ((projection_computes false).comp predecessor_computes).1
  simp only [bodyLabelProgram,outsideLabelProgram,rejectedWordLabelProgram,
    selectLabelProgram,unionLabelProgram,complementLabelProgram,
    mapOutputProgram,pairOutputProgram,reindexProgram,liftNumericalProgram,Closed,fv_lam,fv_app,fv_var,
    (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed),
    (show (numericalIdentity).fv = ∅ from numericalIdentity_computes.1),
    (show (rootLabelSelector 1).fv = ∅ from (rootLabelSelector_computes 1).1),
    (show (complementLabelSelector).fv = ∅ from complementLabelSelector_computes.1),
    (show (constructorNodePartsTerm).fv = ∅ from constructorNodeParts_computes.1),
    (show (numericalCompose (numericalProjectionTerm false) predecessorTerm).fv = ∅ from htail),
    (show (labelSelectorTerm).fv = ∅ from labelSelectorTerm_computes.1),
    (show (jointLeafLabelTerm).fv = ∅ from jointLeafLabelTerm_computes.1),
    (show (emptyLabelProgram).fv = ∅ from (emptyLabelProgram_computes (fun _ => 0)).1),
    (show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1),
    (show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1)]
  rw [hP]
  simp
  decide

theorem differenceLabelProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (differenceLabelProgram P Q).Closed := by
  have htail : (numericalCompose (numericalProjectionTerm false) predecessorTerm).Closed :=
    ((projection_computes false).comp predecessor_computes).1
  simp only [bodyLabelProgram,outsideLabelProgram,differenceLabelProgram,rejectedWordLabelProgram,
    selectLabelProgram,unionLabelProgram,complementLabelProgram,
    mapOutputProgram,pairOutputProgram,reindexProgram,liftNumericalProgram,Closed,fv_lam,fv_app,fv_var,
    (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed),
    (show (numericalIdentity).fv = ∅ from numericalIdentity_computes.1),
    (show (rootLabelSelector 1).fv = ∅ from (rootLabelSelector_computes 1).1),
    (show (complementLabelSelector).fv = ∅ from complementLabelSelector_computes.1),
    (show (constructorNodePartsTerm).fv = ∅ from constructorNodeParts_computes.1),
    (show (numericalCompose (numericalProjectionTerm false) predecessorTerm).fv = ∅ from htail),
    (show (labelSelectorTerm).fv = ∅ from labelSelectorTerm_computes.1),
    (show (jointLeafLabelTerm).fv = ∅ from jointLeafLabelTerm_computes.1),
    (show (emptyLabelProgram).fv = ∅ from (emptyLabelProgram_computes (fun _ => 0)).1),
    (show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1),
    (show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1)]
  rw [hP,hQ]
  simp
  decide

theorem bodyLabelProgram_subst (P V : AlphaTerm) (hV : V.Closed) (x : ℕ) (hx : 40 < x) :
    (bodyLabelProgram P).subst x V = bodyLabelProgram (P.subst x V) := by
  have htail : (numericalCompose (numericalProjectionTerm false) predecessorTerm).Closed :=
    ((projection_computes false).comp predecessor_computes).1
  have hv (i : ℕ) : i ∉ V.fv := by rw [hV]; simp
  have h1 : 1 ≠ x := by omega
  have h2 : 2 ≠ x := by omega
  have h40 : 40 ≠ x := by omega
  simp only [bodyLabelProgram,outsideLabelProgram,rejectedWordLabelProgram,
    selectLabelProgram,unionLabelProgram,complementLabelProgram,
    mapOutputProgram,pairOutputProgram,reindexProgram,liftNumericalProgram,
    subst_lam_fresh _ _ 1 x h1 (hv 1),subst_lam_fresh _ _ 2 x h2 (hv 2),
    subst_lam_fresh _ _ 40 x h40 (hv 40),subst_app,
    subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ numericalIdentity_computes.1,
    subst_closed _ _ _ (rootLabelSelector_computes 1).1,
    subst_closed _ _ _ complementLabelSelector_computes.1,
    subst_closed _ _ _ constructorNodeParts_computes.1,
    subst_closed _ _ _ htail,
    subst_closed _ _ _ labelSelectorTerm_computes.1,
    subst_closed _ _ _ jointLeafLabelTerm_computes.1,
    subst_closed _ _ _ (emptyLabelProgram_computes (fun _ => 0)).1,
    subst_closed _ _ _ (projection_computes true).1,
    subst_closed _ _ _ (projection_computes false).1,
    subst_var,h1,h2,ite_false]

theorem differenceLabelProgram_subst (P Q V : AlphaTerm) (hV : V.Closed) (x : ℕ) (hx : 40 < x) :
    (differenceLabelProgram P Q).subst x V = differenceLabelProgram (P.subst x V) (Q.subst x V) := by
  have htail : (numericalCompose (numericalProjectionTerm false) predecessorTerm).Closed :=
    ((projection_computes false).comp predecessor_computes).1
  have hv (i : ℕ) : i ∉ V.fv := by rw [hV]; simp
  have h1 : 1 ≠ x := by omega
  have h2 : 2 ≠ x := by omega
  have h40 : 40 ≠ x := by omega
  simp only [bodyLabelProgram,outsideLabelProgram,differenceLabelProgram,rejectedWordLabelProgram,
    selectLabelProgram,unionLabelProgram,complementLabelProgram,
    mapOutputProgram,pairOutputProgram,reindexProgram,liftNumericalProgram,
    subst_lam_fresh _ _ 1 x h1 (hv 1),subst_lam_fresh _ _ 2 x h2 (hv 2),
    subst_lam_fresh _ _ 40 x h40 (hv 40),subst_app,
    subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ numericalIdentity_computes.1,
    subst_closed _ _ _ (rootLabelSelector_computes 1).1,
    subst_closed _ _ _ complementLabelSelector_computes.1,
    subst_closed _ _ _ constructorNodeParts_computes.1,
    subst_closed _ _ _ htail,
    subst_closed _ _ _ labelSelectorTerm_computes.1,
    subst_closed _ _ _ jointLeafLabelTerm_computes.1,
    subst_closed _ _ _ (emptyLabelProgram_computes (fun _ => 0)).1,
    subst_closed _ _ _ (projection_computes true).1,
    subst_closed _ _ _ (projection_computes false).1,
    subst_var,h1,h2,ite_false]

/-- Normalize input syntax once, then substitute into fixed label-program templates. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform tree Borel-label indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let $M_p$ be the named term decoded from $p$ if that term is closed, and the fixed named zero
    numeral otherwise. Its code is computed by $\LambdaProgramCode$, and its alpha-class is $P_p$.
    Fix named representatives $M,N,U$ of the three templates
    $$F_{x_{86}},\qquad D_{x_{86},x_{87}},\qquad
    \lambdaab{o}{x_{86}(\lambdaab{n}{\ChurchNumeral{0}})},$$
    using binders different from the placeholder variables. Define
    $$\begin{aligned}
    N_p&:=\SubstLambda{N}{x_{86}}{M_p},\\
    f(p)&:=\LambdaSyntaxCode{\SubstLambda{M}{x_{86}}{M_p}},\\
    d(p,q)&:=\LambdaSyntaxCode{\SubstLambda{N_p}{x_{87}}{M_q}},\\
    u(p)&:=\LambdaSyntaxCode{\SubstLambda{U}{x_{86}}{M_p}}.
    \end{aligned}$$
    The syntax-substitution generators of §{sec:lambda-index-recursion} compute these maps by beta
    reduction. Closed substitutions commute with the displayed program constructors, so decoding
    gives the asserted alpha-classes. No placeholder remains free. The representatives are fixed
    before the input numbers; the finite closedness test and substitutions never run the input programs.
    The preceding label-program lemma proves correctness of the first two generated programs. For the
    last, substitute the constant-zero function into the original beta/query derivation. Every query
    is then answered by beta reduction, and the unused outer input may be arbitrary.
-/
theorem uniform_tree_borel_label_indices :
    ∃ (F G : AlphaTerm) (f g : ℕ → ℕ), NumericalComputes F f ∧ NumericalComputes G g ∧
      (∀ p, (Term.decode (f p)).fv = ∅ ∧
        Term.closedProgram (f p) = bodyLabelProgram (Term.closedProgram p)) ∧
      ∀ p q, (Term.decode (g (Nat.pair p q))).fv = ∅ ∧
        Term.closedProgram (g (Nat.pair p q)) =
          differenceLabelProgram (Term.closedProgram p) (Term.closedProgram q) := by
  have hN : NumericalComputes programCodeTerm (fun e => (Term.programSyntax e).code) :=
    ⟨programCodeTerm_closed,programCodeTerm_apply⟩
  obtain ⟨F,f,hF,hf⟩ := uniform_template_indices (bodyLabelProgram (var 86)) 86
  obtain ⟨G,g,hG,hg⟩ := uniform_binary_template_indices (differenceLabelProgram (var 86) (var 87)) 86 87
  have hF' := hF.comp hN
  have hG' := hG.comp ((hN.comp (projection_computes true)).pair (hN.comp (projection_computes false)))
  refine ⟨_,_,_,_,hF',hG',?_,?_⟩
  · intro p
    have h := hf (Term.programSyntax p).code
    simp only [Term.decode_code,Term.mk_programSyntax] at h
    rw [bodyLabelProgram_subst _ _ (Term.closedProgram_closed p) 86 (by decide)] at h
    simp only [subst_var,ite_true] at h
    have hc : (Term.decode (f (Term.programSyntax p).code)).fv = ∅ := by
      change (mk (Term.decode (f (Term.programSyntax p).code))).Closed
      rw [h]
      exact bodyLabelProgram_closed (Term.closedProgram_closed p)
    exact ⟨hc,(ite_eq_left hc).trans h⟩
  · intro p q
    simp only [Nat.unpair_pair,Bool.false_eq_true,ite_true,ite_false]
    have h := hg (Term.programSyntax p).code (Term.programSyntax q).code
    simp only [Term.decode_code,Term.mk_programSyntax] at h
    rw [differenceLabelProgram_subst _ _ _ (Term.closedProgram_closed p) 86 (by decide),
      differenceLabelProgram_subst _ _ _ (Term.closedProgram_closed q) 87 (by decide)] at h
    norm_num only [subst_var,ite_true,ite_false,subst_closed _ _ _ (Term.closedProgram_closed p)] at h
    have hc : (Term.decode (g (Nat.pair (Term.programSyntax p).code (Term.programSyntax q).code))).fv = ∅ := by
      change (mk (Term.decode (g (Nat.pair (Term.programSyntax p).code (Term.programSyntax q).code)))).Closed
      rw [h]
      exact differenceLabelProgram_closed (Term.closedProgram_closed p) (Term.closedProgram_closed q)
    exact ⟨hc,(ite_eq_left hc).trans h⟩

/-- Turn the zero-parameter tree program into one that ignores its input function. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform tree Borel-label indices
-/
theorem uniform_pure_tree_indices :
    ∃ F f, NumericalComputes F f ∧ ∀ p,
      (Term.decode (f p)).fv = ∅ ∧ Term.closedProgram (f p) = pureTreeProgram (Term.closedProgram p) := by
  have hN : NumericalComputes programCodeTerm (fun e => (Term.programSyntax e).code) :=
    ⟨programCodeTerm_closed,programCodeTerm_apply⟩
  obtain ⟨F,f,hF,hf⟩ := uniform_template_indices (pureTreeProgram (var 86)) 86
  refine ⟨_,_,hF.comp hN,fun p => ?_⟩
  have h := hf (Term.programSyntax p).code
  simp only [Term.decode_code,Term.mk_programSyntax] at h
  have hc0 := (numericalConstant_computes 0).1
  rw [pureTreeProgram,liftNumericalProgram,
    subst_lam_fresh _ _ 40 86 (by decide) (by rw [Term.closedProgram_closed]; simp)] at h
  simp only [subst_app,subst_var,ite_true,subst_closed _ _ _ hc0] at h
  have hc : (Term.decode (f (Term.programSyntax p).code)).fv = ∅ := by
    change (mk (Term.decode (f (Term.programSyntax p).code))).Closed
    rw [h]
    unfold Closed
    rw [fv_lam,fv_app,Term.closedProgram_closed,hc0]
    simp
  exact ⟨hc,(ite_eq_left hc).trans h⟩

/-- Both label maps use the same iterated-jump input as the stage tree decider. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For the stage family of the preceding theorem, suppose the initial tree is recursive and a stage
    $a$ has stabilized. The program $P_{r(a)}$ decides $T_a$ at
    $\chi_{(\IteratedJump{\emptyset}{g(a)})'}$. A pure numerical decider for the initial tree can be run
    at the same parameter by ignoring its input function. The proposition therefore computes both
    $C_{T_a}$ and $D_{T,T_a}$ at this parameter. The closed-tree recursion theorem identifies
    $\TreeBody{T_a}$ as the greatest perfect subset of $\TreeBody{T}$, so these are respectively Borel
    codes for the perfect kernel and the scattered part. Their label maps require no jump beyond the
    one already used by the stage decider. This conclusion concerns a specified stage of a recursive
    well-order presentation; obtaining that stage uniformly from a supplied ordinal notation is a
    separate step.
-/
theorem recursive_stage_borel_codes (W : WellOrderPresentation (fun _ => 0))
    (P : AlphaTerm) (hP : P.Closed) :
    ∃ (G Q : AlphaTerm) (g r : ℕ → ℕ), NumericalComputes G g ∧ NumericalComputes Q r ∧
      ∃ hv : ∀ a : W.Carrier, KleeneNotation.Valid (g a.val),
      ∀ (T : Set (List Bool)), IsSubtree T → Decides (fun _ => 0) P (codedTree T) →
      ∀ a : W.Carrier,
      let S := stageTree W.order ((inferInstance : WellFounded W.order)) T a
      let ε := jumpName (characteristic (KleeneNotation.iteratedJump ∅ (g a.val) (hv a)))
      Computes ε (bodyLabelProgram (Term.closedProgram (r a.val))) (bodyCode S).val ∧
      Computes ε (differenceLabelProgram (pureTreeProgram P) (Term.closedProgram (r a.val)))
        (differenceCode T S).val := by
  obtain ⟨G,Q,g,r,hG,hQ,hv,hstage⟩ := recursive_cantor_stage_deciders W P hP
  refine ⟨G,Q,g,r,hG,hQ,hv,fun T hT hp a => ?_⟩
  have h0 : characteristic (∅ : Set ℕ) = fun _ => 0 := by
    funext n; simp [characteristic]
  have hs := hstage ∅ T hT (by simpa only [h0] using hp) a
  exact ⟨bodyLabelProgram_computes hs,differenceLabelProgram_computes (pureTreeProgram_decides hp _) hs⟩

/-- Stabilization identifies the closed code as the greatest perfect subset. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For the stage family of the preceding theorem, suppose the initial tree is recursive and a stage
    $a$ has stabilized. The program $P_{r(a)}$ decides $T_a$ at
    $\chi_{(\IteratedJump{\emptyset}{g(a)})'}$. A pure numerical decider for the initial tree can be run
    at the same parameter by ignoring its input function. The proposition therefore computes both
    $C_{T_a}$ and $D_{T,T_a}$ at this parameter. The closed-tree recursion theorem identifies
    $\TreeBody{T_a}$ as the greatest perfect subset of $\TreeBody{T}$, so these are respectively Borel
    codes for the perfect kernel and the scattered part. Their label maps require no jump beyond the
    one already used by the stage decider. This conclusion concerns a specified stage of a recursive
    well-order presentation; obtaining that stage uniformly from a supplied ordinal notation is a
    separate step.
-/
theorem stable_stage_codes {ι : Type*} (R : ι → ι → Prop) (hR : WellFounded R)
    (T : Set (List Bool)) (a : ι)
    (ha : treeBody (stageTree R hR T a) = derivedSet (treeBody (stageTree R hR T a))) :
    let K := (bodyCode (stageTree R hR T a)).value binaryCylinderBasis
    Perfect K ∧ K ⊆ treeBody T ∧
      (∀ P : Set (ℕ → Bool), Perfect P → P ⊆ treeBody T → P ⊆ K) ∧
      (differenceCode T (stageTree R hR T a)).value binaryCylinderBasis = treeBody T \ K := by
  simp only [value_bodyCode,value_differenceCode]
  obtain ⟨hperf,hsub,hmax⟩ := stable_stage_greatest R hR T a ha
  exact ⟨hperf,hsub,hmax,True.intro⟩

end CantorDerivative
end PolishSpaceBook
