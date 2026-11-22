module

public import PolishSpaceBook.LambdaRankLabelStep
public import PolishSpaceBook.LambdaRecursiveTrees

@[expose] public section

/-! # A total lambda program for the finite labels of rank expressions -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm BorelExpression
namespace RankBound
open LambdaRelative
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem emptyLabel_eq (w : List ℕ) :
    (if NatListCode.encode w = 0 then 2 else if NatListCode.encode w ≤ 1 then 3 else 0) =
      complement (basic 0) w := by
  have h0 : NatListCode.encode w = 0 ↔ w = [] := by
    simpa only [NatListCode.encode] using
      (show NatListCode.encode w = NatListCode.encode [] ↔ w = [] from
        NatListCode.encode_injective.eq_iff)
  have h1 : NatListCode.encode w = 1 ↔ w = [0] := by
    simpa [NatListCode.encode,Nat.pair] using
      (show NatListCode.encode w = NatListCode.encode [0] ↔ w = [0] from
        NatListCode.encode_injective.eq_iff)
  simp only [Nat.le_one_iff_eq_zero_or_eq_one,h0,h1]
  cases w with
  | nil => simp [complement,graft]
  | cons i w =>
    cases w with
    | nil => by_cases hi : i = 0 <;> simp [hi,complement,graft,basic,absent]
    | cons j w => by_cases hi : i = 0 <;> simp [hi,complement,graft,basic,absent]

def augmentedState (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (z : ℕ) : ℕ := Nat.pair z (Nat.pair
      (E (edgeInputValue z).unpair.1 (edgeInputValue z).unpair.2.unpair.1
        (NatListCode.decode (edgeInputValue z).unpair.2.unpair.2))
      (if R (relationInputValue z).unpair.1 (relationInputValue z).unpair.2 then 1 else 0))

theorem selector_active (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (i a s : ℕ) (w : List ℕ) :
    rankStepSelectorValue (augmentedState E R
      (Nat.pair (i+1) (Nat.pair a (Nat.pair s (NatListCode.encode w))))) = update E R a s w := by
  simp only [
    boundFieldValue,
    nodeFieldValue,
    wordFieldValue,
    wordEntry0Value,
    wordEntry1Value,
    wordEntry2Value,
    wordEntry3Value,
    wordEntry4Value,
    wordTailValue,
    edgeInputValue,
    relationInputValue,
    selectorStateValue,
    selectorTagValue,
    selectorLengthValue,
    selectorEntry0Value,
    selectorEntry1Value,
    selectorEntry2Value,
    selectorEntry3Value,
    selectorEntry4Value,
    selectorTailValue,
    selectorEdgeValue,
    selectorRelationValue,
    nextRankStateValue,
    emptyTailLabelValue,
    rankStepSelectorValue,
    augmentedState,
    Nat.unpair_pair,
    NatListCode.decode_encode]
  rcases w with _ | ⟨j,w⟩
  · simp [update,doneState]
  cases j with
  | succ j => simp [update,doneState,List.getD]
  | zero =>
    rcases w with _ | ⟨t,w⟩
    · simp [update,doneState,List.getD]
    rcases w with _ | ⟨j,w⟩
    · simp [update,doneState,List.getD]
    cases j with
    | succ j => simp [update,doneState,List.getD]
    | zero =>
      rcases w with _ | ⟨j,w⟩
      · simp [update,doneState,List.getD]
      cases j with
      | zero =>
        rcases w with _ | ⟨j,w⟩
        · simp [update,doneState,List.getD]
        cases j <;> simp [update,doneState,List.getD] <;> split_ifs <;> omega
      | succ j =>
        rcases w with _ | ⟨b,w⟩
        · simp [update,doneState,List.getD]
        by_cases hr : R b a
        · simp [update,queryState,List.getD,hr]; split_ifs <;> omega
        · simp [update,doneState,List.getD,hr]
          rw [← emptyLabel_eq w]
          split_ifs <;> omega


theorem selector_correct (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (z : ℕ) : rankStepSelectorValue (augmentedState E R z) = stateStep E R z := by
  obtain ⟨i,p,rfl⟩ : ∃ i p, z = Nat.pair i p :=
    ⟨z.unpair.1,z.unpair.2,(Nat.pair_unpair z).symm⟩
  cases i with
  | zero =>
    simp [rankStepSelectorValue,selectorTagValue,selectorStateValue,augmentedState,stateStep]
  | succ i =>
    obtain ⟨a,q,rfl⟩ : ∃ a q, p = Nat.pair a q :=
      ⟨p.unpair.1,p.unpair.2,(Nat.pair_unpair p).symm⟩
    obtain ⟨s,w,rfl⟩ : ∃ s w, q = Nat.pair s w :=
      ⟨q.unpair.1,q.unpair.2,(Nat.pair_unpair q).symm⟩
    simpa [stateStep] using selector_active E R i a s (NatListCode.decode w)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the rank-label program, let $P$ compute the edge label $e_{t,s}(v)$ from
    $\NatPair{t}{\NatPair{s}{\LambdaListCode{v}}}$, and let $Q$ decide $R(b,a)$ from
    $\NatPair{b}{a}$, returning one for truth and zero for falsity. Both must be total at the fixed
    parameter. The desired labels obey the finite-word equations in §{sec:edst-borel-rank-layers}.
    Labels zero, one, and two mean absence, union, and complement; a leaf for the whole space has label three.
    Use the numerical states
    $$d(m):=\NatPair{0}{m},\qquad
    q(a,s,v):=\NatPair{1}{\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}}.$$
    The first is finished; the second requests a rank label. These states are numerical data for lambda terms.
-/
theorem rankStepProgram_computes {ε : ℕ → ℕ} {P Q : AlphaTerm}
    (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (hP : Computes ε P (fun z : ℕ => E z.unpair.1 z.unpair.2.unpair.1
      (NatListCode.decode z.unpair.2.unpair.2)))
    (hQ : Decides ε Q (fun z : ℕ => R z.unpair.1 z.unpair.2)) :
    Computes ε (rankStepProgram P Q) (stateStep E R) := by
  have hq : Computes ε Q (fun z : ℕ => if R z.unpair.1 z.unpair.2 then 1 else 0) :=
    ⟨hQ.1,fun z => hQ.runs z⟩
  have h := rankStepProgram_computes_aux hP hq
  refine ⟨h.1,fun z => ?_⟩
  simpa only [← selector_correct E R z,augmentedState] using h.2 z

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
def rankLabelProgram (P Q : AlphaTerm) : AlphaTerm :=
  mapOutputProgram (numericalProjectionTerm false)
    (reindexProgram (relativeIterationProgram (rankStepProgram P Q)) rankIterationInputTerm)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Store either an unfinished query $(a,s,v)$ or a finished label $m$ as a natural number, with a tag
    distinguishing the two cases. One update follows the finite-word equations. It either returns a finished
    label, using the edge program when needed, or replaces $(a,s,v)$ by $(b,t,u)$ after reading the first
    five entries of $v$ and checking $R(b,a)$. Finished states are left fixed. The update is a closed lambda
    program built from numerical pairs, list operations, comparisons, and the two supplied programs.
    Iterate it $|v|+1$ times by a Church numeral and read the finished label. Every unfinished update
    shortens the word by five entries, so induction on the number of updates proves that this bound suffices.
    Each update preserves the label specified by the finite-word equations, and all calls retain the same
    oracle parameter. For well-founded $R$, the preceding lemma identifies this label with
    $\RankLayerCode{a}{s}(v)$. The explicit terms and their reduction proof are given in
    §{sec:lambda-borel-constructor-programs}.
-/
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
theorem rankLabelProgram_computes {ε : ℕ → ℕ} {P Q : AlphaTerm}
    (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (hP : Computes ε P (fun z : ℕ => E z.unpair.1 z.unpair.2.unpair.1
      (NatListCode.decode z.unpair.2.unpair.2)))
    (hQ : Decides ε Q (fun z : ℕ => R z.unpair.1 z.unpair.2)) :
    Computes ε (rankLabelProgram P Q) (fun z : ℕ =>
      labels E R z.unpair.1 z.unpair.2.unpair.1 (NatListCode.decode z.unpair.2.unpair.2)) := by
  have h := ((rankStepProgram_computes E R hP hQ).iterate.reindex rankIterationInput_computes).map
    (projection_computes false)
  refine ⟨h.1,fun z => ?_⟩
  have hs := iterate_query E R z.unpair.1 z.unpair.2.unpair.1
    (NatListCode.decode z.unpair.2.unpair.2) ((NatListCode.decode z.unpair.2.unpair.2).length + 1)
    (by omega)
  have hinit : Nat.pair 1 z = queryState z.unpair.1 z.unpair.2.unpair.1
      (NatListCode.decode z.unpair.2.unpair.2) := by simp [queryState]
  have hz := h.2 z
  simpa [rankLabelProgram,rankIterationInputValue,initialRankStateValue,hinit,hs,doneState] using hz

/-- Fixing the rank and source-node arguments gives a label program on finite words. -/
def rankCodeLabelProgram (P Q : AlphaTerm) (a s : ℕ) : AlphaTerm :=
  reindexProgram (rankLabelProgram P Q)
    (pairNumerical (numericalConstant a) (pairNumerical (numericalConstant s) numericalIdentity))

local instance rankLabelListEncoding : Encodable (List ℕ) := NatListCode.encodable

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Computable labels of rank expressions
  excerpt: |
    Fix $\varepsilon$. Suppose one closed lambda program computes $e_{t,s}(v)$ from
    $\NatPair{t}{\NatPair{s}{\LambdaListCode{v}}}$ for all $t,s,v$, and another decides $R(b,a)$
    from $\NatPair{b}{a}$, both relative to $\varepsilon$. Then one closed program computes
    $\RankLayerCode{a}{s}(v)$ jointly in $a,s,v$ at the same parameter.
    The finite-word equations remain computable without well-foundedness of $R$; when $R$ is well founded
    and the edge expressions are valid, the output is the label map of the valid expression for $\RankLayer{a}{s}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Correctness of the rank-label program
  excerpt: |
    Under the totality and computation hypotheses on $P,Q$, the program
    $\LambdaRankLabelProgram{P}{Q}$ computes the finite-word rank labels at the original parameter.
    If $R$ is well founded and every $e_{t,s}$ is valid, fixing $a,s$ gives a program for
    $\RankLayerCode{a}{s}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    First run $P,Q$ on the inputs $U(z),V(z)$ and form the augmented state. Their totality justifies
    these calls even when the selector will not use their answers. The numerical reduction rules for
    $Z$ give a finished state at each terminal case of the finite-word equations. The zero tag leaves
    finished states fixed. The only unfinished output is $N$: here the word starts with $(0,t,0,j,b)$,
    where $j>0$ and $R(b,a)$ holds, and the new state is $q(b,t,u)$ for the remaining suffix $u$.
    Thus each update preserves the requested label and each unfinished update consumes five entries.

    More precisely, induction on $n$ proves the following: if $n>|v|$, updating $q(a,s,v)$ that many
    times gives the finished state with the prescribed label. If the first update reaches a finished state, all remaining
    updates leave that state finished.
    In the unfinished case the suffix has length $|v|-5$, and the remaining $n-1$ updates exceed this
    length, so the induction hypothesis applies. Both subtractions here occur only when $|v|\ge5$ and $n>0$.
    Apply the iterator with $n=|v|+1$ and project the second component. Its reduction theorem gives a
    finite beta/query derivation of the label. No step changes the oracle. For well-founded $R$, the
    finite-label lemma identifies the output with the label of the valid rank expression. Finally,
    pairing constants for $a,s$ with the input word code gives the fixed-parameter label program.
-/
theorem rankCodeLabelProgram_computes {ε : ℕ → ℕ} {P Q : AlphaTerm}
    (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) [DecidableRel R] (hR : WellFounded R)
    (hP : Computes ε P (fun z : ℕ => (E z.unpair.1 z.unpair.2.unpair.1).val
      (NatListCode.decode z.unpair.2.unpair.2)))
    (hQ : Decides ε Q (fun z : ℕ => R z.unpair.1 z.unpair.2)) (a s : ℕ) :
    Computes ε (rankCodeLabelProgram P Q a s) (code E R hR a s).val := by
  have h := (rankLabelProgram_computes (fun t s => (E t s).val) R hP hQ).reindex
    ((numericalConstant_computes a).pair ((numericalConstant_computes s).pair numericalIdentity_computes))
  refine ⟨h.1,fun w => ?_⟩
  simpa [rankCodeLabelProgram,Encodable.encode,code_val_eq_labels] using h.2 (NatListCode.encode w)

end RankBound
end PolishSpaceBook
