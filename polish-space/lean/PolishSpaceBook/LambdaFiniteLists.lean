module

public import PolishSpaceBook.LambdaNumericalComparison
public import PolishSpaceBook.LambdaNumericalProjections
public import Mathlib.Logic.Equiv.List

@[expose] public section

/-! # Numerically coded finite lists and lambda recursion

This is the same zero/paired-successor coding used for reduction certificates.
All program correctness statements concern ordinary beta reduction of actual
closed lambda terms, with no auxiliary computational language.
-/
namespace PolishSpaceBook.NamedLambda
namespace NatListCode

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Finite lists store an ordered sequence of numerical data. We encode them by natural numbers so that the same arithmetic and comparison programs apply to their entries and codes. The corner notation $\LambdaListCode{\ell}$
    denotes the natural-number code of the list $\ell$, while $\ChurchNumeral{\LambdaListCode{\ell}}$
    is the closed lambda term representing that number. For a finite list $\ell$ of natural numbers, set
    $$\LambdaListCode{[]}:=0,\qquad
    \LambdaListCode{a::\ell}:=\NatPair{a}{\LambdaListCode{\ell}}+1.$$
    Define $\LambdaListDecode{0}:=[]$. For $e>0$, unpair $e-1$, use the first component as the head, and recursively decode the second component as the tail. The tail code is at most $e-1$, hence smaller than $e$, so this recursion terminates.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use the numbering from §{sec:lambda-finite-lists}:
    $$\LambdaListCode{[]}=0,\qquad
    \LambdaListCode{a::s}=p(a,\LambdaListCode{s})+1,$$
    where $p$ is the numerical pairing of the preceding section. Its inverse is $\LambdaListDecode{n}$.
-/
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
def encode : List ℕ → ℕ
  | [] => 0
  | a :: xs => Nat.pair a (encode xs) + 1

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Every natural number decodes to a finite list. The empty-list code is zero, and list access returns entry $j$ when
    $j<|s|$, and zero otherwise. List recursion may return a numeral, a pair, or a function. Indexed recursion retains its
    parameters in both the initial value and the update; only the updates actually visited must terminate.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use the numbering from §{sec:lambda-finite-lists}:
    $$\LambdaListCode{[]}=0,\qquad
    \LambdaListCode{a::s}=p(a,\LambdaListCode{s})+1,$$
    where $p$ is the numerical pairing of the preceding section. Its inverse is $\LambdaListDecode{n}$.
-/
def decode : ℕ → List ℕ
  | 0 => []
  | e + 1 => (Nat.unpair e).1 :: decode (Nat.unpair e).2
termination_by e => e
decreasing_by have := Nat.unpair_right_le e; omega

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induction on the list proves the first identity using the inverse equations for pairing. For the second, use strong induction on the code. Zero is immediate. At a positive code, the tail has smaller code, so the induction hypothesis recovers it; pairing the unchanged head with that tail and adding one recovers the original code.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Coding finite lists
-/
@[simp] theorem decode_encode (xs : List ℕ) : decode (encode xs) = xs := by
  induction xs with
  | nil => simp [encode, decode]
  | cons a xs ih => simp [encode, decode, ih]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Coding finite lists
-/
@[simp] theorem encode_decode (e : ℕ) : encode (decode e) = e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => simp [encode, decode]
    | succ e =>
      rw [decode, encode, ih _ (by have := Nat.unpair_right_le e; omega), Nat.pair_unpair]

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    We use the concrete list coding constructed in §{sec:lambda-finite-lists} for this bijection.
    Thus corner notation for finite sequences has the same meaning in the classical and computational chapters.
-/
/-- The book's concrete list code is the canonical mathlib finite-address numbering. -/
theorem encode_eq_denumerable (xs : List ℕ) :
    encode xs = Denumerable.eqv (List ℕ) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change Nat.pair a (encode xs) + 1 = Nat.pair a (Encodable.encode xs) + 1
    exact congrArg (fun n => Nat.pair a n + 1) ih

/-- The decoder used in Borel-code serialization is the concrete list decoder. -/
theorem decode_eq_denumerable (n : ℕ) :
    decode n = (Denumerable.eqv (List ℕ)).symm n := by
  apply (Denumerable.eqv (List ℕ)).injective
  rw [← encode_eq_denumerable, encode_decode, Equiv.apply_symm_apply]

end NatListCode
namespace AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The constructor and field programs are
    $$\begin{aligned}
    \LambdaListCons&:=\lambdaab{a}{\lambdaab{d}{\LambdaSucc(\LambdaNumericPair\,a\,d)}},\\
    \LambdaListField{i}&:=\lambdaab{e}{\LambdaNumericProjection{i}(\LambdaPred\,e)}
     \qquad(i=1,2).
    \end{aligned}$$
    The first field is the head, and the second is the tail code. The field equations below are asserted for nonempty lists; no head of the empty list is needed.
-/
def listConsBody (A D : AlphaTerm) : AlphaTerm :=
  app successorTerm (app (app numericalPairTerm A) D)

theorem listConsBody_fv (A D : AlphaTerm) :
    (listConsBody A D).fv = A.fv ∪ D.fv := by
  ext x
  simp only [listConsBody, fv_app, (show successorTerm.fv = ∅ from successorTerm_closed), (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listConsBody_subst (A D W : AlphaTerm) (x : ℕ) :
    (listConsBody A D).subst x W =
      listConsBody (A.subst x W) (D.subst x W) := by
  simp only [listConsBody, subst_app, subst_closed _ _ _ successorTerm_closed, subst_closed _ _ _ numericalPairTerm_closed]

def listConsTerm : AlphaTerm := (lam 30 (lam 31 (listConsBody (var 30) (var 31))))

@[simp] theorem listConsTerm_closed : listConsTerm.Closed := by
  unfold listConsTerm Closed
  simp only [fv_lam, listConsBody_fv, fv_var]
  decide

theorem listConsTerm_start {A D : AlphaTerm}
    (hA : A.Closed) (hD : D.Closed) :
    Relation.ReflTransGen Beta (app (app listConsTerm A) D)
      (listConsBody A D) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfA : A.fv = ∅ := hA
  have hfD : D.fv = ∅ := hD
  have h0 : Beta (app (lam 30 (lam 31 (listConsBody (var 30) (var 31)))) A) (lam 31 (listConsBody A (var 31))) := by
    convert Beta.contract 30 (lam 31 (listConsBody (var 30) (var 31))) A using 1

    simp [subst_lam_fresh, subst_var, listConsBody_subst, hfA]
  have h1 : Beta (app (lam 31 (listConsBody A (var 31))) D) (listConsBody A D) := by
    convert Beta.contract 31 (listConsBody A (var 31)) D using 1

    simp [subst_var, listConsBody_subst, subst_closed, hA]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) D).trans
  exact (Relation.ReflTransGen.single h1)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: List constructors and fields
-/
theorem listConsTerm_apply (a d : ℕ) :
    Relation.ReflTransGen Beta (app (app listConsTerm (numeral a)) (numeral d))
      (numeral (Nat.pair a d + 1)) :=
  (listConsTerm_start (numeral_closed a) (numeral_closed d)).trans
    ((beta_steps_app_right successorTerm (numericalPairTerm_apply a d)).trans
      (successorTerm_apply _))

def listFieldBody (first : Bool) (E : AlphaTerm) : AlphaTerm :=
  app (numericalProjectionTerm first) (app predecessorTerm E)

theorem listFieldBody_fv (first : Bool) (E : AlphaTerm) : (listFieldBody first E).fv = E.fv := by
  simp only [listFieldBody, fv_app]
  rw [numericalProjectionTerm_closed, predecessorTerm_closed]
  simp

theorem listFieldBody_subst (first : Bool) (E W : AlphaTerm) (x : ℕ) :
    (listFieldBody first E).subst x W = listFieldBody first (E.subst x W) := by
  simp only [listFieldBody, subst_app, subst_closed _ _ _ (numericalProjectionTerm_closed first),
    subst_closed _ _ _ predecessorTerm_closed]

def listFieldTerm (first : Bool) : AlphaTerm := lam 30 (listFieldBody first (var 30))

@[simp] theorem listFieldTerm_closed (first : Bool) : (listFieldTerm first).Closed := by
  unfold listFieldTerm Closed
  simp [fv_lam, listFieldBody_fv, fv_var]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For the constructor, two beta steps expose numerical pairing followed by successor. For each field, one beta step exposes predecessor followed by numerical projection. The input to predecessor is positive, so it returns the pair code. The projection equations then give the indicated component. All constants are closed and every displayed variable is bound.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: List constructors and fields
-/
theorem listFieldTerm_cons (first : Bool) (a d : ℕ) :
    Relation.ReflTransGen Beta (app (listFieldTerm first) (numeral (Nat.pair a d + 1)))
      (numeral (if first then a else d)) := by
  have h : Beta (app (listFieldTerm first) (numeral (Nat.pair a d + 1)))
      (listFieldBody first (numeral (Nat.pair a d + 1))) := by
    convert Beta.contract 30 (listFieldBody first (var 30)) (numeral (Nat.pair a d + 1)) using 1
    · rfl
    · simp [listFieldBody_subst, subst_var]
  apply (Relation.ReflTransGen.single h).trans
  have hp := predecessorTerm_apply (Nat.pair a d + 1)
  simp only [Nat.add_sub_cancel] at hp
  exact (beta_steps_app_right (numericalProjectionTerm first) hp).trans
    (numericalProjectionTerm_pair first a d)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For closed terms $Z,H$, construct a list recursor by self-application. With fresh distinct binders $s,e$, put
    $$\begin{aligned}
    B(Z,H,R,e)&:=\LambdaZeroTest\,e\,Z\\
     &\qquad\bigl(H(\LambdaListField{1}\,e)(R(\LambdaListField{2}\,e))\bigr),\\
    K_{Z,H}&:=\lambdaab{s}{\lambdaab{e}{B(Z,H,ss,e)}},\\
    \LambdaListFold{Z}{H}&:=K_{Z,H}K_{Z,H},\\
    \LambdaListRecursor&:=\lambdaab{h}{\lambdaab{z}{\LambdaListFold{z}{h}}}.
    \end{aligned}$$
    Expand the abbreviations before abstraction. In the last line keep the binders of each kernel distinct from $h,z$. The zero branch returns the base value; the other branch passes the head and recursively computed tail value to $H$. The wrapper $\LambdaListRecursor$ supplies the handler and base value as inputs to one closed program.
-/
def listFoldBody (Z H R E : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm E) Z)
    (app (app H (app (listFieldTerm true) E)) (app R (app (listFieldTerm false) E)))

theorem listFoldBody_fv (Z H R E : AlphaTerm) :
    (listFoldBody Z H R E).fv = Z.fv ∪ H.fv ∪ R.fv ∪ E.fv := by
  simp only [listFoldBody, fv_app]
  rw [zeroTestTerm_closed, listFieldTerm_closed, listFieldTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listFoldBody_subst (Z H R E W : AlphaTerm) (x : ℕ) :
    (listFoldBody Z H R E).subst x W =
      listFoldBody (Z.subst x W) (H.subst x W) (R.subst x W) (E.subst x W) := by
  simp only [listFoldBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ (listFieldTerm_closed true), subst_closed _ _ _ (listFieldTerm_closed false)]

def listFoldKernel (Z H : AlphaTerm) : AlphaTerm :=
  lam 12 (lam 13 (listFoldBody Z H (app (var 12) (var 12)) (var 13)))

def listFold (Z H : AlphaTerm) : AlphaTerm := app (listFoldKernel Z H) (listFoldKernel Z H)

theorem listFold_fv (Z H : AlphaTerm) : (listFold Z H).fv = ((Z.fv ∪ H.fv).erase 13).erase 12 := by
  simp only [listFold, listFoldKernel, fv_app, fv_lam, listFoldBody_fv, fv_var]
  ext x
  simp
  tauto

theorem listFold_closed {Z H : AlphaTerm} (hZ : Z.Closed) (hH : H.Closed) :
    (listFold Z H).Closed := by
  unfold Closed
  rw [listFold_fv, hZ, hH]; simp

theorem listFold_subst (Z H W : AlphaTerm) (x : ℕ) (hx12 : 12 ≠ x) (hx13 : 13 ≠ x)
    (h12 : 12 ∉ W.fv) (h13 : 13 ∉ W.fv) :
    (listFold Z H).subst x W = listFold (Z.subst x W) (H.subst x W) := by
  simp only [listFold, listFoldKernel, subst_app,
    subst_lam_fresh _ _ 12 x hx12 h12, subst_lam_fresh _ _ 13 x hx13 h13,
    listFoldBody_subst, subst_var, ite_eq_right hx12, ite_eq_right hx13]

theorem listFold_unfold {Z H : AlphaTerm} (hZ : Z.Closed) (hH : H.Closed) (e : ℕ) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral e))
      (listFoldBody Z H (listFold Z H) (numeral e)) := by
  let K := listFoldKernel Z H
  have hK : K.Closed := by
    unfold K listFoldKernel Closed
    simp only [fv_lam, listFoldBody_fv, fv_app]
    rw [hZ, hH]; simp [fv_var]; decide
  have hR := listFold_closed hZ hH
  have h₁ : Beta (app K K) (lam 13 (listFoldBody Z H (app K K) (var 13))) := by
    convert Beta.contract 12 (lam 13 (listFoldBody Z H (app (var 12) (var 12)) (var 13))) K using 1
    · rfl
    · rw [subst_lam_fresh _ _ 13 12 (by decide) (by rw [hK]; simp), listFoldBody_subst]
      simp [subst_app, subst_var, subst_closed _ _ _ hZ, subst_closed _ _ _ hH]
  have h₂ : Beta (app (lam 13 (listFoldBody Z H (listFold Z H) (var 13))) (numeral e))
      (listFoldBody Z H (listFold Z H) (numeral e)) := by
    convert Beta.contract 13 (listFoldBody Z H (listFold Z H) (var 13)) (numeral e) using 1
    simp [listFoldBody_subst, subst_var, subst_closed _ _ _ hZ, subst_closed _ _ _ hH,
      subst_closed _ _ _ hR]
  exact .tail (.single (.app_left _ h₁)) h₂

theorem listFold_nil {Z H : AlphaTerm} (hZ : Z.Closed) (hH : H.Closed) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral 0)) Z :=
  (listFold_unfold hZ hH 0).trans (branch_zero _ _ (by rw [hZ]; simp))

theorem listFold_cons {Z H : AlphaTerm} (hZ : Z.Closed) (hH : H.Closed) (a d : ℕ) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral (Nat.pair a d + 1)))
      (app (app H (numeral a)) (app (listFold Z H) (numeral d))) := by
  apply (listFold_unfold hZ hH _).trans
  apply (branch_succ (Nat.pair a d) _ _).trans
  exact beta_steps_app (beta_steps_app_right H (listFieldTerm_cons true a d))
    (beta_steps_app_right (listFold Z H) (listFieldTerm_cons false a d))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Two beta steps unfold the self-application. At code zero, zero testing returns $Z$ and discards the recursive branch. At a nonempty list, the positive branch is selected and the field equations expose its head and tail code. Induct on the list: the empty case uses the assumed reduction of $Z$, and the nonempty case first applies the induction hypothesis to the tail, then uses the hypothesis for $H$. Thus each input list has a finite reduction to its assigned value. Closedness follows from the fresh binders and closed constants. Finally, two beta steps in the wrapper supply $H,Z$ to the same fold. Coding and decoding extend these computations to every numerical input.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Recursion on finite lists by a lambda term
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Every natural number decodes to a finite list. The empty-list code is zero, and list access returns entry $j$ when
    $j<|s|$, and zero otherwise. List recursion may return a numeral, a pair, or a function. Indexed recursion retains its
    parameters in both the initial value and the update; only the updates actually visited must terminate.
-/
theorem listFold_apply {Z H : AlphaTerm} (hZ : Z.Closed) (hH : H.Closed)
    (f : List ℕ → AlphaTerm) (h0 : Relation.ReflTransGen Beta Z (f []))
    (hs : ∀ a xs, Relation.ReflTransGen Beta (app (app H (numeral a)) (f xs)) (f (a :: xs)))
    (xs : List ℕ) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral (NatListCode.encode xs))) (f xs) := by
  induction xs with
  | nil => exact (listFold_nil hZ hH).trans h0
  | cons a xs ih =>
    exact (listFold_cons hZ hH a _).trans
      ((beta_steps_app_right (app H (numeral a)) ih).trans (hs a xs))

/-- The two-argument wrapper supplies the fold's handler and base value at run time. -/
def listRecursorTerm : AlphaTerm := lam 30 (lam 31 (listFold (var 31) (var 30)))

@[simp] theorem listRecursorTerm_closed : listRecursorTerm.Closed := by
  unfold listRecursorTerm Closed
  simp only [fv_lam, listFold_fv, fv_var]
  decide

theorem listRecursorTerm_start {H Z : AlphaTerm} (hH : H.Closed) (hZ : Z.Closed) :
    Relation.ReflTransGen Beta (app (app listRecursorTerm H) Z) (listFold Z H) := by
  have hfH : H.fv = ∅ := hH
  have hfZ : Z.fv = ∅ := hZ
  have h₁ : Beta (app listRecursorTerm H) (lam 31 (listFold (var 31) H)) := by
    convert Beta.contract 30 (lam 31 (listFold (var 31) (var 30))) H using 1
    · rfl
    · simp [subst_lam_fresh, listFold_subst, subst_var, hfH]
  have h₂ : Beta (app (lam 31 (listFold (var 31) H)) Z) (listFold Z H) := by
    convert Beta.contract 31 (listFold (var 31) H) Z using 1
    simp [listFold_subst, subst_var, hfZ, subst_closed _ _ _ hH]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Recursion on finite lists by a lambda term
-/
theorem listRecursorTerm_apply {H Z : AlphaTerm} (hH : H.Closed) (hZ : Z.Closed)
    (f : List ℕ → AlphaTerm) (h0 : Relation.ReflTransGen Beta Z (f []))
    (hs : ∀ a xs, Relation.ReflTransGen Beta (app (app H (numeral a)) (f xs)) (f (a :: xs)))
    (xs : List ℕ) :
    Relation.ReflTransGen Beta (app (app (app listRecursorTerm H) Z) (numeral (NatListCode.encode xs)))
      (f xs) :=
  (beta_steps_app_left (listRecursorTerm_start hH hZ) _).trans (listFold_apply hZ hH f h0 hs xs)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Write $\ListConcat{\ell}{m}$ for concatenation and $\ListMap{f}{\ell}$ for applying $f$ to every element, in order. Define
    $$\begin{aligned}
    \LambdaListAppend&:=\lambdaab{e}{\lambdaab{d}{\LambdaListRecursor\,\LambdaListCons\,d\,e}},\\
    M&:=\lambdaab{f}{\lambdaab{a}{\lambdaab{r}{\LambdaListCons\,(fa)\,r}}},\\
    \LambdaListMap&:=\lambdaab{f}{\lambdaab{e}{\LambdaListRecursor\,(Mf)\,\ChurchNumeral{0}\,e}},\\
    T&:=\lambdaab{f}{\lambdaab{a}{\lambdaab{r}{\LambdaZeroTest\,(fa)\,r\,\ChurchNumeral{1}}}},\\
    \LambdaListAny&:=\lambdaab{f}{\lambdaab{e}{\LambdaListRecursor\,(Tf)\,\ChurchNumeral{0}\,e}},\\
    \LambdaListMember&:=\lambdaab{x}{\lambdaab{e}{\LambdaListAny\,(\LambdaEqual\,x)\,e}}.
    \end{aligned}$$
    These are closed terms. The map handler constructs the new head from the transformed element. The existence handler keeps the tail's answer when the head fails its test, and returns one when the head succeeds.
-/
def listAppendBody (E D : AlphaTerm) : AlphaTerm :=
  app (app (app listRecursorTerm listConsTerm) D) E

theorem listAppendBody_fv (E D : AlphaTerm) :
    (listAppendBody E D).fv = E.fv ∪ D.fv := by
  ext x
  simp only [listAppendBody, fv_app, (show listRecursorTerm.fv = ∅ from listRecursorTerm_closed), (show listConsTerm.fv = ∅ from listConsTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listAppendBody_subst (E D W : AlphaTerm) (x : ℕ) :
    (listAppendBody E D).subst x W =
      listAppendBody (E.subst x W) (D.subst x W) := by
  simp only [listAppendBody, subst_app, subst_closed _ _ _ listRecursorTerm_closed, subst_closed _ _ _ listConsTerm_closed]

def listAppendTerm : AlphaTerm := (lam 30 (lam 31 (listAppendBody (var 30) (var 31))))

@[simp] theorem listAppendTerm_closed : listAppendTerm.Closed := by
  unfold listAppendTerm Closed
  simp only [fv_lam, listAppendBody_fv, fv_var]
  decide

theorem listAppendTerm_start {E D : AlphaTerm}
    (hE : E.Closed) (hD : D.Closed) :
    Relation.ReflTransGen Beta (app (app listAppendTerm E) D)
      (listAppendBody E D) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfD : D.fv = ∅ := hD
  have h0 : Beta (app (lam 30 (lam 31 (listAppendBody (var 30) (var 31)))) E) (lam 31 (listAppendBody E (var 31))) := by
    convert Beta.contract 30 (lam 31 (listAppendBody (var 30) (var 31))) E using 1

    simp [subst_lam_fresh, subst_var, listAppendBody_subst, hfE]
  have h1 : Beta (app (lam 31 (listAppendBody E (var 31))) D) (listAppendBody E D) := by
    convert Beta.contract 31 (listAppendBody E (var 31)) D using 1

    simp [subst_var, listAppendBody_subst, subst_closed, hE]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) D).trans
  exact (Relation.ReflTransGen.single h1)

def listMapHandlerBody (F A R : AlphaTerm) : AlphaTerm :=
  app (app listConsTerm (app F A)) R

theorem listMapHandlerBody_fv (F A R : AlphaTerm) :
    (listMapHandlerBody F A R).fv = F.fv ∪ A.fv ∪ R.fv := by
  ext x
  simp only [listMapHandlerBody, fv_app, (show listConsTerm.fv = ∅ from listConsTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listMapHandlerBody_subst (F A R W : AlphaTerm) (x : ℕ) :
    (listMapHandlerBody F A R).subst x W =
      listMapHandlerBody (F.subst x W) (A.subst x W) (R.subst x W) := by
  simp only [listMapHandlerBody, subst_app, subst_closed _ _ _ listConsTerm_closed]

def listMapHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (listMapHandlerBody (var 30) (var 31) (var 32)))))

@[simp] theorem listMapHandlerTerm_closed : listMapHandlerTerm.Closed := by
  unfold listMapHandlerTerm Closed
  simp only [fv_lam, listMapHandlerBody_fv, fv_var]
  decide

theorem listMapHandlerTerm_start {F A R : AlphaTerm}
    (hF : F.Closed) (hA : A.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app listMapHandlerTerm F) A) R)
      (listMapHandlerBody F A R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfF : F.fv = ∅ := hF
  have hfA : A.fv = ∅ := hA
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (listMapHandlerBody (var 30) (var 31) (var 32))))) F) (lam 31 (lam 32 (listMapHandlerBody F (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (listMapHandlerBody (var 30) (var 31) (var 32)))) F using 1

    simp [subst_lam_fresh, subst_var, listMapHandlerBody_subst, hfF]
  have h1 : Beta (app (lam 31 (lam 32 (listMapHandlerBody F (var 31) (var 32)))) A) (lam 32 (listMapHandlerBody F A (var 32))) := by
    convert Beta.contract 31 (lam 32 (listMapHandlerBody F (var 31) (var 32))) A using 1

    simp [subst_lam_fresh, subst_var, listMapHandlerBody_subst, subst_closed, hF, hfA]
  have h2 : Beta (app (lam 32 (listMapHandlerBody F A (var 32))) R) (listMapHandlerBody F A R) := by
    convert Beta.contract 32 (listMapHandlerBody F A (var 32)) R using 1

    simp [subst_var, listMapHandlerBody_subst, subst_closed, hF, hA]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) R).trans
  exact (Relation.ReflTransGen.single h2)

def listMapBody (F E : AlphaTerm) : AlphaTerm :=
  app (app (app listRecursorTerm (app listMapHandlerTerm F)) (numeral 0)) E

theorem listMapBody_fv (F E : AlphaTerm) :
    (listMapBody F E).fv = F.fv ∪ E.fv := by
  ext x
  simp only [listMapBody, fv_app, (show listRecursorTerm.fv = ∅ from listRecursorTerm_closed), (show listMapHandlerTerm.fv = ∅ from listMapHandlerTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listMapBody_subst (F E W : AlphaTerm) (x : ℕ) :
    (listMapBody F E).subst x W =
      listMapBody (F.subst x W) (E.subst x W) := by
  simp only [listMapBody, subst_app, subst_closed _ _ _ listRecursorTerm_closed, subst_closed _ _ _ listMapHandlerTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ decide membership in the pair trees $T,S$, taking a numerical pair of word codes and
    returning zero or one. We give the numerical tests and the joint edge-label program needed by
    §{sec:edst-recursive-borel-completeness}. All computations use the original oracle argument $o$.
    In this subsection abbreviate
    $$\begin{aligned}
    p_i&:=\LambdaNumericProjection{i},&A_i&:=\LambdaListMap\,p_i,\\
    \langle X,Y\rangle_\lambda&:=\LambdaNumericPair\,X\,Y,&
    \ell(X)&:=\LambdaListLength\,X,\\
    C(X,Y;U,V)&:=\LambdaLeCase{X}{Y}{U}{V},&
    L(X,Y)&:=C(\LambdaSucc\,X,Y;\ChurchNumeral{1},\ChurchNumeral{0}).
    \end{aligned}$$
    Thus $A_i$ projects every entry of a word, and $L$ tests strict numerical inequality.
    Expand each abbreviation before abstraction, with fresh bound variables.
-/
def listMapTerm : AlphaTerm := (lam 30 (lam 31 (listMapBody (var 30) (var 31))))

@[simp] theorem listMapTerm_closed : listMapTerm.Closed := by
  unfold listMapTerm Closed
  simp only [fv_lam, listMapBody_fv, fv_var]
  decide

theorem listMapTerm_start {F E : AlphaTerm}
    (hF : F.Closed) (hE : E.Closed) :
    Relation.ReflTransGen Beta (app (app listMapTerm F) E)
      (listMapBody F E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfF : F.fv = ∅ := hF
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (lam 31 (listMapBody (var 30) (var 31)))) F) (lam 31 (listMapBody F (var 31))) := by
    convert Beta.contract 30 (lam 31 (listMapBody (var 30) (var 31))) F using 1

    simp [subst_lam_fresh, subst_var, listMapBody_subst, hfF]
  have h1 : Beta (app (lam 31 (listMapBody F (var 31))) E) (listMapBody F E) := by
    convert Beta.contract 31 (listMapBody F (var 31)) E using 1

    simp [subst_var, listMapBody_subst, subst_closed, hF]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) E).trans
  exact (Relation.ReflTransGen.single h1)

def listAnyHandlerBody (F A R : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app F A)) R) (numeral 1)

theorem listAnyHandlerBody_fv (F A R : AlphaTerm) :
    (listAnyHandlerBody F A R).fv = F.fv ∪ A.fv ∪ R.fv := by
  ext x
  simp only [listAnyHandlerBody, fv_app, (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed) ,(show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listAnyHandlerBody_subst (F A R W : AlphaTerm) (x : ℕ) :
    (listAnyHandlerBody F A R).subst x W =
      listAnyHandlerBody (F.subst x W) (A.subst x W) (R.subst x W) := by
  simp only [listAnyHandlerBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed ,subst_closed _ _ _ (numeral_closed 1)]

def listAnyHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (listAnyHandlerBody (var 30) (var 31) (var 32)))))

@[simp] theorem listAnyHandlerTerm_closed : listAnyHandlerTerm.Closed := by
  unfold listAnyHandlerTerm Closed
  simp only [fv_lam, listAnyHandlerBody_fv, fv_var]
  decide

theorem listAnyHandlerTerm_start {F A R : AlphaTerm}
    (hF : F.Closed) (hA : A.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app listAnyHandlerTerm F) A) R)
      (listAnyHandlerBody F A R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfF : F.fv = ∅ := hF
  have hfA : A.fv = ∅ := hA
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (listAnyHandlerBody (var 30) (var 31) (var 32))))) F) (lam 31 (lam 32 (listAnyHandlerBody F (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (listAnyHandlerBody (var 30) (var 31) (var 32)))) F using 1

    simp [subst_lam_fresh, subst_var, listAnyHandlerBody_subst, hfF]
  have h1 : Beta (app (lam 31 (lam 32 (listAnyHandlerBody F (var 31) (var 32)))) A) (lam 32 (listAnyHandlerBody F A (var 32))) := by
    convert Beta.contract 31 (lam 32 (listAnyHandlerBody F (var 31) (var 32))) A using 1

    simp [subst_lam_fresh, subst_var, listAnyHandlerBody_subst, subst_closed, hF, hfA]
  have h2 : Beta (app (lam 32 (listAnyHandlerBody F A (var 32))) R) (listAnyHandlerBody F A R) := by
    convert Beta.contract 32 (listAnyHandlerBody F A (var 32)) R using 1

    simp [subst_var, listAnyHandlerBody_subst, subst_closed, hF, hA]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) R).trans
  exact (Relation.ReflTransGen.single h2)

def listAnyBody (F E : AlphaTerm) : AlphaTerm :=
  app (app (app listRecursorTerm (app listAnyHandlerTerm F)) (numeral 0)) E

theorem listAnyBody_fv (F E : AlphaTerm) :
    (listAnyBody F E).fv = F.fv ∪ E.fv := by
  ext x
  simp only [listAnyBody, fv_app, (show listRecursorTerm.fv = ∅ from listRecursorTerm_closed), (show listAnyHandlerTerm.fv = ∅ from listAnyHandlerTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listAnyBody_subst (F E W : AlphaTerm) (x : ℕ) :
    (listAnyBody F E).subst x W =
      listAnyBody (F.subst x W) (E.subst x W) := by
  simp only [listAnyBody, subst_app, subst_closed _ _ _ listRecursorTerm_closed, subst_closed _ _ _ listAnyHandlerTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def listAnyTerm : AlphaTerm := (lam 30 (lam 31 (listAnyBody (var 30) (var 31))))

@[simp] theorem listAnyTerm_closed : listAnyTerm.Closed := by
  unfold listAnyTerm Closed
  simp only [fv_lam, listAnyBody_fv, fv_var]
  decide

theorem listAnyTerm_start {F E : AlphaTerm}
    (hF : F.Closed) (hE : E.Closed) :
    Relation.ReflTransGen Beta (app (app listAnyTerm F) E)
      (listAnyBody F E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfF : F.fv = ∅ := hF
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (lam 31 (listAnyBody (var 30) (var 31)))) F) (lam 31 (listAnyBody F (var 31))) := by
    convert Beta.contract 30 (lam 31 (listAnyBody (var 30) (var 31))) F using 1

    simp [subst_lam_fresh, subst_var, listAnyBody_subst, hfF]
  have h1 : Beta (app (lam 31 (listAnyBody F (var 31))) E) (listAnyBody F E) := by
    convert Beta.contract 31 (listAnyBody F (var 31)) E using 1

    simp [subst_var, listAnyBody_subst, subst_closed, hF]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) E).trans
  exact (Relation.ReflTransGen.single h1)

def listMemberBody (X E : AlphaTerm) : AlphaTerm :=
  app (app listAnyTerm (app equalityTerm X)) E

theorem listMemberBody_fv (X E : AlphaTerm) :
    (listMemberBody X E).fv = X.fv ∪ E.fv := by
  ext x
  simp only [listMemberBody, fv_app, (show listAnyTerm.fv = ∅ from listAnyTerm_closed), (show equalityTerm.fv = ∅ from equalityTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem listMemberBody_subst (X E W : AlphaTerm) (x : ℕ) :
    (listMemberBody X E).subst x W =
      listMemberBody (X.subst x W) (E.subst x W) := by
  simp only [listMemberBody, subst_app, subst_closed _ _ _ listAnyTerm_closed, subst_closed _ _ _ equalityTerm_closed]

def listMemberTerm : AlphaTerm := (lam 30 (lam 31 (listMemberBody (var 30) (var 31))))

@[simp] theorem listMemberTerm_closed : listMemberTerm.Closed := by
  unfold listMemberTerm Closed
  simp only [fv_lam, listMemberBody_fv, fv_var]
  decide

theorem listMemberTerm_start {X E : AlphaTerm}
    (hX : X.Closed) (hE : E.Closed) :
    Relation.ReflTransGen Beta (app (app listMemberTerm X) E)
      (listMemberBody X E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfX : X.fv = ∅ := hX
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (lam 31 (listMemberBody (var 30) (var 31)))) X) (lam 31 (listMemberBody X (var 31))) := by
    convert Beta.contract 30 (lam 31 (listMemberBody (var 30) (var 31))) X using 1

    simp [subst_lam_fresh, subst_var, listMemberBody_subst, hfX]
  have h1 : Beta (app (lam 31 (listMemberBody X (var 31))) E) (listMemberBody X E) := by
    convert Beta.contract 31 (listMemberBody X (var 31)) E using 1

    simp [subst_var, listMemberBody_subst, subst_closed, hX]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) E).trans
  exact (Relation.ReflTransGen.single h1)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For concatenation, use the code of the second list as the base value and the list constructor as the handler. Induction on the first list then prepends exactly its elements. For mapping, use the empty-list code as the base. At each head, the reduction assumed for $F$ computes the new element and the constructor prepends it to the already mapped tail.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Finite-list operations by lambda terms
-/
theorem listAppendTerm_code (xs ys : List ℕ) :
    Relation.ReflTransGen Beta
      (app (app listAppendTerm (numeral (NatListCode.encode xs))) (numeral (NatListCode.encode ys)))
      (numeral (NatListCode.encode (xs ++ ys))) := by
  apply (listAppendTerm_start (numeral_closed _) (numeral_closed _)).trans
  exact listRecursorTerm_apply listConsTerm_closed (numeral_closed _)
    (fun xs => numeral (NatListCode.encode (xs ++ ys))) .refl
    (fun a xs => listConsTerm_apply a (NatListCode.encode (xs ++ ys))) xs

theorem listAppendTerm_apply (e d : ℕ) :
    Relation.ReflTransGen Beta (app (app listAppendTerm (numeral e)) (numeral d))
      (numeral (NatListCode.encode (NatListCode.decode e ++ NatListCode.decode d))) := by
  simpa only [NatListCode.encode_decode] using listAppendTerm_code (NatListCode.decode e) (NatListCode.decode d)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Finite-list operations by lambda terms
-/
theorem listMapTerm_code {F : AlphaTerm} (hc : F.Closed) (f : ℕ → ℕ)
    (hf : ∀ a, Relation.ReflTransGen Beta (app F (numeral a)) (numeral (f a))) (xs : List ℕ) :
    Relation.ReflTransGen Beta (app (app listMapTerm F) (numeral (NatListCode.encode xs)))
      (numeral (NatListCode.encode (xs.map f))) := by
  apply (listMapTerm_start hc (numeral_closed _)).trans
  apply listRecursorTerm_apply (closed_app listMapHandlerTerm_closed hc) (numeral_closed 0)
    (fun xs => numeral (NatListCode.encode (xs.map f))) .refl _ xs
  intro a xs
  apply (listMapHandlerTerm_start hc (numeral_closed a) (numeral_closed _)).trans
  exact (beta_steps_app_left (beta_steps_app_right listConsTerm (hf a)) _).trans
    (listConsTerm_apply (f a) (NatListCode.encode (xs.map f)))

theorem listMapTerm_apply {F : AlphaTerm} (hc : F.Closed) (f : ℕ → ℕ)
    (hf : ∀ a, Relation.ReflTransGen Beta (app F (numeral a)) (numeral (f a))) (e : ℕ) :
    Relation.ReflTransGen Beta (app (app listMapTerm F) (numeral e))
      (numeral (NatListCode.encode ((NatListCode.decode e).map f))) := by
  simpa only [NatListCode.encode_decode] using listMapTerm_code hc f hf (NatListCode.decode e)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For existence, use zero as the base value. At a head where the predicate is false, zero testing retains the tail's answer; where it is true, it returns one. Induction on the list gives exactly the stated existential condition. Membership is the special case obtained by taking equality with the given number as the predicate. In each case, the list-recursion theorem supplies the finite reduction, and the outer beta steps supply the parameters. The code-decoding identities give the arbitrary-code statements.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Finite-list operations by lambda terms
-/
theorem listAnyTerm_code {F : AlphaTerm} (hc : F.Closed) (p : ℕ → Bool)
    (hp : ∀ a, Relation.ReflTransGen Beta (app F (numeral a)) (numeral (if p a then 1 else 0)))
    (xs : List ℕ) :
    Relation.ReflTransGen Beta (app (app listAnyTerm F) (numeral (NatListCode.encode xs)))
      (numeral (if xs.any p then 1 else 0)) := by
  apply (listAnyTerm_start hc (numeral_closed _)).trans
  apply listRecursorTerm_apply (closed_app listAnyHandlerTerm_closed hc) (numeral_closed 0)
    (fun xs => numeral (if xs.any p then 1 else 0)) .refl _ xs
  intro a xs
  apply (listAnyHandlerTerm_start hc (numeral_closed a) (numeral_closed _)).trans
  unfold listAnyHandlerBody
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm (hp a)) _) _).trans
  cases h : p a with
  | false =>
    simp only [h, Bool.false_eq_true, ite_false, List.any_cons, Bool.false_or]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)
  | true =>
    simp only [h, ite_true, List.any_cons, Bool.true_or]
    exact branch_succ 0 _ _

theorem listAnyTerm_apply {F : AlphaTerm} (hc : F.Closed) (p : ℕ → Bool)
    (hp : ∀ a, Relation.ReflTransGen Beta (app F (numeral a)) (numeral (if p a then 1 else 0)))
    (e : ℕ) :
    Relation.ReflTransGen Beta (app (app listAnyTerm F) (numeral e))
      (numeral (if (NatListCode.decode e).any p then 1 else 0)) := by
  simpa only [NatListCode.encode_decode] using listAnyTerm_code hc p hp (NatListCode.decode e)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Finite-list operations by lambda terms
-/
theorem listMemberTerm_code (x : ℕ) (xs : List ℕ) :
    Relation.ReflTransGen Beta (app (app listMemberTerm (numeral x)) (numeral (NatListCode.encode xs)))
      (numeral (if x ∈ xs then 1 else 0)) := by
  apply (listMemberTerm_start (numeral_closed x) (numeral_closed _)).trans
  have h := listAnyTerm_code (closed_app equalityTerm_closed (numeral_closed x))
    (fun a => decide (x = a)) (fun a => by simpa using equalityTerm_apply x a) xs
  have hb : xs.any (fun a => decide (x = a)) = true ↔ x ∈ xs := by
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨x, hx, rfl⟩
  simpa only [listMemberBody, hb] using h

theorem listMemberTerm_apply (x e : ℕ) :
    Relation.ReflTransGen Beta (app (app listMemberTerm (numeral x)) (numeral e))
      (numeral (if x ∈ NatListCode.decode e then 1 else 0)) := by
  simpa only [NatListCode.encode_decode] using listMemberTerm_code x (NatListCode.decode e)


end AlphaTerm
end PolishSpaceBook.NamedLambda
