module

public import PolishSpaceBook.LambdaListAccess
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # Taking prefixes and deciding the prefix relation

The numerical recursor appends the next list entry while the index is in
range, then keeps the completed list. All programs are closed lambda terms.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Pointwise numerical comparison and branch selection. -/
def numericalIfLe (A B X Y : AlphaTerm) : AlphaTerm :=
  lam 40 (chooseLeBody (app A (var 40)) (app B (var 40)) (app X (var 40)) (app Y (var 40)))

theorem NumericalComputes.ifLe {A B X Y : AlphaTerm} {a b x y : ℕ → ℕ}
    (hA : NumericalComputes A a) (hB : NumericalComputes B b)
    (hX : NumericalComputes X x) (hY : NumericalComputes Y y) :
    NumericalComputes (numericalIfLe A B X Y) (fun n => if a n ≤ b n then x n else y n) := by
  refine ⟨?_,fun n => ?_⟩
  · unfold numericalIfLe Closed
    simp only [fv_lam,chooseLeBody_fv,fv_app,fv_var]
    rw [hA.1,hB.1,hX.1,hY.1]; simp
  · have hs : Beta (app (numericalIfLe A B X Y) (numeral n))
        (chooseLeBody (app A (numeral n)) (app B (numeral n))
          (app X (numeral n)) (app Y (numeral n))) := by
      simpa only [numericalIfLe,chooseLeBody_subst,subst_app,subst_var,ite_true,
        subst_closed _ _ _ hA.1,subst_closed _ _ _ hB.1,
        subst_closed _ _ _ hX.1,subst_closed _ _ _ hY.1] using
        Beta.contract 40 (chooseLeBody (app A (var 40)) (app B (var 40))
          (app X (var 40)) (app Y (var 40))) (numeral n)
    exact (Relation.ReflTransGen.single hs).trans
      ((chooseLeBody_steps (hA.2 n) (hB.2 n) (hX.2 n) (hY.2 n)).trans (chooseLeBody_apply _ _ _ _))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    To extract a prefix, retain the original list code $e$ and accumulate the output code $r$. At stage $k$, append
    the $k$th entry only if that entry exists. The following abbreviations are expanded inside the displayed
    abstractions:
    $$\begin{aligned}
    A(e,k,r)&:=\LambdaListAppend\,r\,
     \bigl(\LambdaListCons\,(\LambdaListGet\,(\LambdaNumericPair\,e\,k))\,\ChurchNumeral{0}\bigr),\\
    J(e,k,r)&:=\LambdaLeCase{\LambdaSucc\,k}{\LambdaListLength\,e}{A(e,k,r)}{r},\\
    B&:=\lambdaab{e}{\ChurchNumeral{0}},\qquad
    H:=\lambdaab{e}{\lambdaab{k}{\lambdaab{r}{J(e,k,r)}}},\\
    \LambdaListTake&:=\lambdaab{z}{\LambdaParamRec{B}{H}\,
     (\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.
    \end{aligned}$$
    The comparison in $J$ is $k+1\le|\LambdaListDecode{e}|$. If it fails, the previous output code is retained.
-/
def listTakeStepIndex := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
def listTakeStepValue := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
def listTakeStepEntry := numericalCompose listGetTerm (pairNumerical (numericalProjectionTerm true) listTakeStepIndex)
def listTakeStepSingleton := numericalCombine listConsTerm listTakeStepEntry (numericalConstant 0)
def listTakeStepAppend := numericalCombine listAppendTerm listTakeStepValue listTakeStepSingleton

def listTakeStep := numericalIfLe
  (numericalCompose successorTerm listTakeStepIndex)
  (numericalCompose listLengthTerm (numericalProjectionTerm true))
  listTakeStepAppend listTakeStepValue

def listTakeStepValueFn (z : ℕ) : ℕ :=
  let xs := NatListCode.decode z.unpair.1
  let k := z.unpair.2.unpair.1
  let r := z.unpair.2.unpair.2
  if k+1 ≤ xs.length then NatListCode.encode (NatListCode.decode r ++ [xs.getD k 0]) else r

theorem listTakeStep_computes : NumericalComputes listTakeStep listTakeStepValueFn := by
  have he := projection_computes true
  have hk : NumericalComputes listTakeStepIndex (fun z => z.unpair.2.unpair.1) :=
    (projection_computes true).comp (projection_computes false)
  have hr : NumericalComputes listTakeStepValue (fun z => z.unpair.2.unpair.2) :=
    (projection_computes false).comp (projection_computes false)
  have hget : NumericalComputes listTakeStepEntry
      (fun z => (NatListCode.decode z.unpair.1).getD z.unpair.2.unpair.1 0) := by
    simpa [listTakeStepEntry] using listGet_computes.comp (he.pair hk)
  have hsingle : NumericalComputes listTakeStepSingleton
      (fun z => NatListCode.encode [(NatListCode.decode z.unpair.1).getD z.unpair.2.unpair.1 0]) :=
    hget.combine (numericalConstant_computes 0) listConsTerm_closed
      (fun a d => Nat.pair a d + 1) listConsTerm_apply
  have happ : NumericalComputes listTakeStepAppend
      (fun z => NatListCode.encode (NatListCode.decode z.unpair.2.unpair.2 ++
        [(NatListCode.decode z.unpair.1).getD z.unpair.2.unpair.1 0])) := by
    simpa only [listTakeStepAppend,NatListCode.decode_encode] using
      hr.combine hsingle listAppendTerm_closed
        (fun a b => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode b)) listAppendTerm_apply
  exact (successor_computes.comp hk).ifLe (listLength_computes.comp he) happ hr

def listTakeTerm := numericalRecursion (numericalConstant 0) listTakeStep

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Induct on the number of recursion steps. Initially the accumulator is the empty-list code. If $k<|s|$, list
    access returns the $k$th entry, the constructor makes its singleton list, and concatenation appends that entry
    to the prefix already accumulated. If $k\ge|s|$, the comparison selects the unchanged accumulator, which
    already codes all of $s$. These are exactly the two cases for taking $k+1$ entries. Numerical primitive
    recursion realizes this recurrence by beta reduction. Every component is closed and total, including list
    access outside its range, so the construction works for every code and every requested length.
-/
theorem listTake_recursion (e n : ℕ) :
    primitiveRec 0 (fun k r => listTakeStepValueFn (Nat.pair e (Nat.pair k r))) n =
      NatListCode.encode ((NatListCode.decode e).take n) := by
  induction n with
  | zero => simp [primitiveRec,NatListCode.encode]
  | succ n ih =>
    rw [primitiveRec,ih]
    simp only [listTakeStepValueFn,Nat.unpair_pair,NatListCode.decode_encode]
    by_cases hn : n < (NatListCode.decode e).length
    · rw [ite_eq_left (by omega),List.take_succ_eq_append_getElem hn]
      congr 2
      simp [List.getD,hn]
    · rw [ite_eq_right (by omega),List.take_of_length_le (by omega : (NatListCode.decode e).length ≤ n),
        List.take_of_length_le (by omega : (NatListCode.decode e).length ≤ n+1)]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Prefix extraction by a lambda term
-/
theorem listTake_computes : NumericalComputes listTakeTerm
    (fun z => NatListCode.encode ((NatListCode.decode z.unpair.1).take z.unpair.2)) := by
  simpa only [listTakeTerm,listTake_recursion] using
    numericalRecursion_computes (numericalConstant_computes 0) listTakeStep_computes

/-- Compare the first list with a prefix of the second of the same length. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the prefix test by
    $$\begin{aligned}
    P(e,d)&:=\LambdaEqual\,e\,
     \bigl(\LambdaListTake\,(\LambdaNumericPair\,d\,(\LambdaListLength\,e))\bigr),\\
    \LambdaListPrefix&:=\lambdaab{z}{P(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z)}.
    \end{aligned}$$
    Expand $P$ inside the abstraction.
-/
def listPrefixTerm := numericalCombine equalityTerm (numericalProjectionTerm true)
  (numericalCompose listTakeTerm (pairNumerical (numericalProjectionTerm false)
    (numericalCompose listLengthTerm (numericalProjectionTerm true))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Prefix decision
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    A list is a prefix of another exactly when it equals the first list's length of entries taken from the second.
    The extraction term computes that prefix, and injectivity of list coding turns list equality into equality
    of the numerical codes. The numerical equality term supplies the stated answer. This includes the empty list
    and the case where the first list is longer than the second.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the prefix test by
    $$\begin{aligned}
    P(e,d)&:=\LambdaEqual\,e\,
     \bigl(\LambdaListTake\,(\LambdaNumericPair\,d\,(\LambdaListLength\,e))\bigr),\\
    \LambdaListPrefix&:=\lambdaab{z}{P(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z)}.
    \end{aligned}$$
    Expand $P$ inside the abstraction.
-/
theorem listPrefix_computes : NumericalComputes listPrefixTerm
    (fun z => if (NatListCode.decode z.unpair.1).IsPrefix (NatListCode.decode z.unpair.2) then 1 else 0) := by
  have ht := listTake_computes.comp
    ((projection_computes false).pair (listLength_computes.comp (projection_computes true)))
  have h := (projection_computes true).combine ht equalityTerm_closed
    (fun a b => if a = b then 1 else 0) equalityTerm_apply
  unfold listPrefixTerm
  convert h using 1
  funext z
  simp only [Nat.unpair_pair,Bool.false_eq_true,ite_false,ite_true]
  have he : z.unpair.1 = NatListCode.encode
      ((NatListCode.decode z.unpair.2).take (NatListCode.decode z.unpair.1).length) ↔
      (NatListCode.decode z.unpair.1).IsPrefix (NatListCode.decode z.unpair.2) := by
    rw [List.prefix_iff_eq_take]
    constructor
    · intro h; simpa only [listTakeStepAppend,NatListCode.decode_encode] using congrArg NatListCode.decode h
    · intro h; simpa only [NatListCode.encode_decode] using congrArg NatListCode.encode h
  simp only [he]

end PolishSpaceBook.NamedLambda.AlphaTerm
