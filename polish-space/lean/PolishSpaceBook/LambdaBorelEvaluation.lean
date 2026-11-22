module

public import PolishSpaceBook.BorelExpressionNatCertificates
public import PolishSpaceBook.LambdaBoundedPrefixTests
public import PolishSpaceBook.LambdaComplementedCodes

@[expose] public section

/-! # Borel evaluation certificates decided by closed lambda programs

The expression label program is the only parameter-dependent component.
Bounds, finite-word operations, and arithmetic clauses are computed by the
book's numerical lambda terms. Both truth values retain the same parameter.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace BorelExpression
local instance borelListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance borelPairEncoding : Encodable (List ℕ × List ℕ) := LambdaTree.wordPairEncodable
abbrev FinitePrefixPair := List ℕ × List ℕ

def rowWord (i : ℕ) : List ℕ := NatListCode.decode i.unpair.1

def rowChild (i : ℕ) : List ℕ := rowWord i ++ [i.unpair.2]

def rowLeaf (i : ℕ) : List ℕ := NatListCode.decode i.unpair.2

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Recall the finite certificate clauses of §{sec:edst-borel-validity}. A sequence $y\in\BaireSpace$ stores
    $\NatPair{u_s}{j_s}$ at coordinate $\LambdaListCode{s}$: $u_s$ is the truth bit and $j_s$ selects a child when a union
    node is true. For the row $i=\NatPair{\LambdaListCode{s}}{k}$, put $t=s\concat(k)$ and
    $$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,|\LambdaListDecode{k}|\}.$$
-/
def certificatePrefixBound (i : ℕ) : ℕ :=
  max (NatListCode.encode (rowWord i) + 1) (max (NatListCode.encode (rowChild i) + 1)
    (max (NatListCode.encode ([] : List ℕ) + 1) (rowLeaf i).length))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here is an explicit Boolean body for combining these values. All its inputs and outputs are numerals;
    write $\LambdaTermName{equal}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaEqual\,
    \LambdaTermName{left}\, \LambdaTermName{right}$, $\LambdaTermName{zero}( \LambdaTermName{left}):=
    \LambdaTermName{equal}( \LambdaTermName{left}, \ChurchNumeral{0})$, and
    $\LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaLeCase{
    \LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}}$.
    Let $\alpha,\delta$ be the two labels, $\mu,\nu$ the two truth values, $j$ the selected child, $k$ the current child,
    and $\theta$ the cylinder-test bit. Put
    $$\begin{aligned}
    &\LambdaTermName{evalArithmetic}(\alpha,\delta,\mu,\nu,j,k,\theta):=\\
     &\LambdaLeCase{\mu}{\ChurchNumeral{1}}{\ChurchNumeral{1}}{\ChurchNumeral{0}}\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{0}), \LambdaTermName{equal}(
    \mu, \ChurchNumeral{0}))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
    \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}),
     \LambdaTermName{implies}( \LambdaTermName{equal}(j,k), \LambdaTermName{zero}( \LambdaTermName{equal}( \delta,
    \ChurchNumeral{0})) \cdot \LambdaTermName{equal}( \nu, \ChurchNumeral{1}))))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
    \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
     \LambdaTermName{implies}( \LambdaTermName{equal}( \nu, \ChurchNumeral{1}), \LambdaTermName{equal}( \mu,
    \ChurchNumeral{1}))))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{2}),
    \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
     \LambdaTermName{equal}(\LambdaAdd\,\mu\,\nu,\ChurchNumeral{1})))\\
     &{}\cdot \LambdaTermName{implies}(\LambdaTermName{equal}(\alpha,\LambdaAdd\,k\,\ChurchNumeral{3}),
     \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}), \theta) \cdot
    \LambdaTermName{implies}( \theta, \LambdaTermName{equal}( \mu, \ChurchNumeral{1}))).
    \end{aligned}$$
    Products abbreviate nested applications of $\LambdaMul$. Multiply this body by the equality test for the
    prescribed root bit, substitute the accessors just described, and abstract the parameter and row input.
    The resulting closed program $\LambdaTermName{evalRow}_ \zeta$ decides the finite certificate clause with root
    bit $\zeta$.
-/
def certificateArithmetic (a d u v j k : ℕ) (leaf : Prop) : Prop :=
  u ≤ 1 ∧ (a = 0 → u = 0) ∧
  (a = 1 → u = 1 → j = k → d ≠ 0 ∧ v = 1) ∧
  (a = 1 → d ≠ 0 → v = 1 → u = 1) ∧
  (a = 2 → d ≠ 0 → u + v = 1) ∧
  (a = k + 3 → (u = 1 ↔ leaf))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For $\varepsilon\in\{0,1\}$, let $P_i^\varepsilon(a,d)$ be the finite row test with prescribed root bit
    $\varepsilon$. It checks $u_s\le1$, the absent-node, union, complement, and leaf clauses, and
    $u_{\emptySeq}=\varepsilon$, reading the first word $a$ for the point and the second word $d$ for the certificate.
    Its arguments have length $b(i)$, so every coordinate it reads is available. Write $P_i:=P_i^0$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the finite row tester, write its input as $z=\NatPair{i}{\NatPair{\LambdaListCode{\sigma}}{\LambdaListCode{\tau}}}$,
    where $\sigma,\tau$ are point and witness prefixes. Numerical projections recover the row, both word codes, and
    $k$. List access at the codes of $s$, its child, and the root recovers the two components of each stored
    pair. Run the supplied relative label program at the code of $s$ and at $\LambdaTermName{rowChild}i$, retaining
    the same parameter.
    List truncation, length, and numerical equality decide whether $\sigma$ starts with $\LambdaListDecode{k}$.
    This comparison is made on list codes, so no separate list-equality primitive is needed.
-/
def finiteCertificateClause (c : BorelExpression) (b : Bool)
    (i : ℕ) (z : FinitePrefixPair) : Prop :=
  (z.2.getD (NatListCode.encode ([] : List ℕ)) 0).unpair.1 = (if b then 1 else 0) ∧
  certificateArithmetic (c (rowWord i)) (c (rowChild i))
    (z.2.getD (NatListCode.encode (rowWord i)) 0).unpair.1
    (z.2.getD (NatListCode.encode (rowChild i)) 0).unpair.1
    (z.2.getD (NatListCode.encode (rowWord i)) 0).unpair.2 i.unpair.2
    (z.1.take (rowLeaf i).length = rowLeaf i)

def rowChildTerm : AlphaTerm := numericalCombine listAppendTerm (numericalProjectionTerm true)
  (numericalCombine listConsTerm (numericalProjectionTerm false) (numericalConstant 0))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Use the list numbering from §{sec:lambda-finite-lists}. A finite word $s$ has natural-number code
    $\LambdaListCode{s}$; the corresponding closed lambda term is $\ChurchNumeral{\LambdaListCode{s}}$.
    We keep the word, its code, and its numeral distinct. On the row input
    $i=\NatPair{\LambdaListCode{s}}{k}$, the code of its child $s\concat(k)$ is computed by the closed term
    $$\LambdaTermName{rowChild}:=\lambdaab{i}{\LambdaListAppend\,(\LambdaNumericProjection{1}i)\,
     (\LambdaListCons\,(\LambdaNumericProjection{2}i)\,\ChurchNumeral{0})}.$$
    Maximum is computed by the body $\LambdaTermName{maximum}(a,b):=\LambdaLeCase{a}{b}{b}{a}$.
    Write $\upsilon(i)$ for the row bound from the Borel evaluation proposition. It is computed by
    $$\LambdaTermName{evalBound}:=\lambdaab{i}{\LambdaTermName{maximum}(\LambdaSucc(\LambdaNumericProjection{1}i),
     \LambdaTermName{maximum}( \LambdaSucc( \LambdaTermName{rowChild}i), \LambdaTermName{maximum}(
    \ChurchNumeral{1}, \LambdaListLength( \LambdaNumericProjection{2}i))))}.$$
    Expand the abbreviations and bind distinct fresh variables. List concatenation computes exactly the child
    code, and the maximum and successor equations prove that $\LambdaTermName{evalBound} \ChurchNumeral{i}$ returns
    $\ChurchNumeral{ \upsilon(i)}$.
-/
theorem rowChild_computes : NumericalComputes rowChildTerm (fun i => NatListCode.encode (rowChild i)) := by
  have hs := (projection_computes false).combine (numericalConstant_computes 0)
    listConsTerm_closed (fun a d => Nat.pair a d + 1) listConsTerm_apply
  simpa [rowChildTerm,rowChild,rowWord,NatListCode.encode,NatListCode.decode] using
    (projection_computes true).combine hs listAppendTerm_closed
      (fun a b => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode b)) listAppendTerm_apply

def maxTerm (A B : AlphaTerm) := numericalIfLe A B B A
private theorem max_computes {A B : AlphaTerm} {a b : ℕ → ℕ}
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    NumericalComputes (maxTerm A B) (fun n => max (a n) (b n)) := by
  simpa only [maxTerm,max_def] using ha.ifLe hb hb ha

def certificatePrefixBoundTerm := maxTerm (numericalCompose successorTerm (numericalProjectionTerm true))
  (maxTerm (numericalCompose successorTerm rowChildTerm)
    (maxTerm (numericalConstant 1) (numericalCompose listLengthTerm (numericalProjectionTerm false))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Use the list numbering from §{sec:lambda-finite-lists}. A finite word $s$ has natural-number code
    $\LambdaListCode{s}$; the corresponding closed lambda term is $\ChurchNumeral{\LambdaListCode{s}}$.
    We keep the word, its code, and its numeral distinct. On the row input
    $i=\NatPair{\LambdaListCode{s}}{k}$, the code of its child $s\concat(k)$ is computed by the closed term
    $$\LambdaTermName{rowChild}:=\lambdaab{i}{\LambdaListAppend\,(\LambdaNumericProjection{1}i)\,
     (\LambdaListCons\,(\LambdaNumericProjection{2}i)\,\ChurchNumeral{0})}.$$
    Maximum is computed by the body $\LambdaTermName{maximum}(a,b):=\LambdaLeCase{a}{b}{b}{a}$.
    Write $\upsilon(i)$ for the row bound from the Borel evaluation proposition. It is computed by
    $$\LambdaTermName{evalBound}:=\lambdaab{i}{\LambdaTermName{maximum}(\LambdaSucc(\LambdaNumericProjection{1}i),
     \LambdaTermName{maximum}( \LambdaSucc( \LambdaTermName{rowChild}i), \LambdaTermName{maximum}(
    \ChurchNumeral{1}, \LambdaListLength( \LambdaNumericProjection{2}i))))}.$$
    Expand the abbreviations and bind distinct fresh variables. List concatenation computes exactly the child
    code, and the maximum and successor equations prove that $\LambdaTermName{evalBound} \ChurchNumeral{i}$ returns
    $\ChurchNumeral{ \upsilon(i)}$.
-/
theorem certificatePrefixBound_computes : NumericalComputes certificatePrefixBoundTerm certificatePrefixBound := by
  unfold certificatePrefixBound
  simpa [certificatePrefixBoundTerm,rowWord,rowLeaf,NatListCode.encode,Nat.succ_eq_add_one] using
    max_computes (successor_computes.comp (projection_computes true))
      (max_computes (successor_computes.comp rowChild_computes)
        (max_computes (numericalConstant_computes 1) (listLength_computes.comp (projection_computes false))))

private theorem relative_eq {ε : ℕ → ℕ} {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : LambdaRelative.Computes ε F f) (hg : LambdaRelative.Computes ε G g) :
    LambdaRelative.DecidablePredicate ε (fun n => f n = g n) := by
  classical
  have he := (projection_computes true).combine (projection_computes false)
    equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  have h := (hf.pair hg).map he
  refine ⟨_,h.1,fun n => ⟨?_,?_⟩⟩
  · intro hn; simpa [Nat.unpair_pair,hn] using h.2 n
  · intro hn; simpa [Nat.unpair_pair,hn] using h.2 n

private theorem relative_le {ε : ℕ → ℕ} {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : LambdaRelative.Computes ε F f) (hg : LambdaRelative.Computes ε G g) :
    LambdaRelative.DecidablePredicate ε (fun n => f n ≤ g n) := by
  classical
  have he := (projection_computes true).ifLe (projection_computes false)
    (numericalConstant_computes 1) (numericalConstant_computes 0)
  have h := (hf.pair hg).map he
  refine ⟨_,h.1,fun n => ⟨?_,?_⟩⟩
  · intro hn; simpa [Nat.unpair_pair,hn] using h.2 n
  · intro hn; simpa [Nat.unpair_pair,hn] using h.2 n

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here is an explicit Boolean body for combining these values. All its inputs and outputs are numerals;
    write $\LambdaTermName{equal}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaEqual\,
    \LambdaTermName{left}\, \LambdaTermName{right}$, $\LambdaTermName{zero}( \LambdaTermName{left}):=
    \LambdaTermName{equal}( \LambdaTermName{left}, \ChurchNumeral{0})$, and
    $\LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaLeCase{
    \LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}}$.
    Let $\alpha,\delta$ be the two labels, $\mu,\nu$ the two truth values, $j$ the selected child, $k$ the current child,
    and $\theta$ the cylinder-test bit. Put
    $$\begin{aligned}
    &\LambdaTermName{evalArithmetic}(\alpha,\delta,\mu,\nu,j,k,\theta):=\\
     &\LambdaLeCase{\mu}{\ChurchNumeral{1}}{\ChurchNumeral{1}}{\ChurchNumeral{0}}\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{0}), \LambdaTermName{equal}(
    \mu, \ChurchNumeral{0}))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
    \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}),
     \LambdaTermName{implies}( \LambdaTermName{equal}(j,k), \LambdaTermName{zero}( \LambdaTermName{equal}( \delta,
    \ChurchNumeral{0})) \cdot \LambdaTermName{equal}( \nu, \ChurchNumeral{1}))))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
    \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
     \LambdaTermName{implies}( \LambdaTermName{equal}( \nu, \ChurchNumeral{1}), \LambdaTermName{equal}( \mu,
    \ChurchNumeral{1}))))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{2}),
    \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
     \LambdaTermName{equal}(\LambdaAdd\,\mu\,\nu,\ChurchNumeral{1})))\\
     &{}\cdot \LambdaTermName{implies}(\LambdaTermName{equal}(\alpha,\LambdaAdd\,k\,\ChurchNumeral{3}),
     \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}), \theta) \cdot
    \LambdaTermName{implies}( \theta, \LambdaTermName{equal}( \mu, \ChurchNumeral{1}))).
    \end{aligned}$$
    Products abbreviate nested applications of $\LambdaMul$. Multiply this body by the equality test for the
    prescribed root bit, substitute the accessors just described, and abstract the parameter and row input.
    The resulting closed program $\LambdaTermName{evalRow}_ \zeta$ decides the finite certificate clause with root
    bit $\zeta$.
-/
private theorem relative_certificateArithmetic {ε : ℕ → ℕ} {A D U V J K : AlphaTerm}
    {a d u v j k : ℕ → ℕ} {leaf : ℕ → Prop}
    (ha : LambdaRelative.Computes ε A a) (hd : LambdaRelative.Computes ε D d)
    (hu : LambdaRelative.Computes ε U u) (hv : LambdaRelative.Computes ε V v)
    (hj : LambdaRelative.Computes ε J j) (hk : LambdaRelative.Computes ε K k)
    (hl : LambdaRelative.DecidablePredicate ε leaf) :
    LambdaRelative.DecidablePredicate ε
      (fun z => certificateArithmetic (a z) (d z) (u z) (v z) (j z) (k z) (leaf z)) := by
  have hconst := fun n => LambdaRelative.ofNumerical (numericalConstant_computes n) ε
  have ha0 := relative_eq ha (hconst 0)
  have ha1 := relative_eq ha (hconst 1)
  have ha2 := relative_eq ha (hconst 2)
  have hd0 := (relative_eq hd (hconst 0)).not
  have hu0 := relative_eq hu (hconst 0)
  have hu1 := relative_eq hu (hconst 1)
  have hv1 := relative_eq hv (hconst 1)
  have hsum := relative_eq
    ((hu.pair hv).map ((projection_computes true).add (projection_computes false))) (hconst 1)
  have hlabel := relative_eq ha (hk.map (numericalIdentity_computes.add (numericalConstant_computes 3)))
  simpa [certificateArithmetic,iff_iff_implies_and_implies] using
    (relative_le hu (hconst 1)).and (ha0.imp hu0 |>.and
      ((ha1.imp (hu1.imp ((relative_eq hj hk).imp (hd0.and hv1)))).and
        ((ha1.imp (hd0.imp (hv1.imp hu1))).and
          ((ha2.imp (hd0.imp hsum)).and (hlabel.imp ((hu1.imp hl).and (hl.imp hu1)))))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Verification]
    Every accessor terminates by the numerical pairing and list-program theorems. The label calls terminate
    by the hypothesis on the supplied program. Equality and comparison return zero or one; on such bits,
    $\LambdaTermName{implies}$ computes implication, $\LambdaTermName{zero}$ negation, and multiplication
    conjunction. The six displayed factors
    therefore express exactly the truth-bit bound and the five certificate clauses in the main text.
    The additional root test specifies the required evaluation side. Composition preserves the parameter,
    and beta/query reduction gives the claimed answer on every finite input, including insufficient prefixes.
    The outer construction below ensures that only sufficiently long prefixes affect a branch.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the finite row tester, write its input as $z=\NatPair{i}{\NatPair{\LambdaListCode{\sigma}}{\LambdaListCode{\tau}}}$,
    where $\sigma,\tau$ are point and witness prefixes. Numerical projections recover the row, both word codes, and
    $k$. List access at the codes of $s$, its child, and the root recovers the two components of each stored
    pair. Run the supplied relative label program at the code of $s$ and at $\LambdaTermName{rowChild}i$, retaining
    the same parameter.
    List truncation, length, and numerical equality decide whether $\sigma$ starts with $\LambdaListDecode{k}$.
    This comparison is made on list codes, so no separate list-equality primitive is needed.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here is an explicit Boolean body for combining these values. All its inputs and outputs are numerals;
    write $\LambdaTermName{equal}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaEqual\,
    \LambdaTermName{left}\, \LambdaTermName{right}$, $\LambdaTermName{zero}( \LambdaTermName{left}):=
    \LambdaTermName{equal}( \LambdaTermName{left}, \ChurchNumeral{0})$, and
    $\LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaLeCase{
    \LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}}$.
    Let $\alpha,\delta$ be the two labels, $\mu,\nu$ the two truth values, $j$ the selected child, $k$ the current child,
    and $\theta$ the cylinder-test bit. Put
    $$\begin{aligned}
    &\LambdaTermName{evalArithmetic}(\alpha,\delta,\mu,\nu,j,k,\theta):=\\
     &\LambdaLeCase{\mu}{\ChurchNumeral{1}}{\ChurchNumeral{1}}{\ChurchNumeral{0}}\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{0}), \LambdaTermName{equal}(
    \mu, \ChurchNumeral{0}))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
    \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}),
     \LambdaTermName{implies}( \LambdaTermName{equal}(j,k), \LambdaTermName{zero}( \LambdaTermName{equal}( \delta,
    \ChurchNumeral{0})) \cdot \LambdaTermName{equal}( \nu, \ChurchNumeral{1}))))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
    \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
     \LambdaTermName{implies}( \LambdaTermName{equal}( \nu, \ChurchNumeral{1}), \LambdaTermName{equal}( \mu,
    \ChurchNumeral{1}))))\\
     &{} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{2}),
    \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
     \LambdaTermName{equal}(\LambdaAdd\,\mu\,\nu,\ChurchNumeral{1})))\\
     &{}\cdot \LambdaTermName{implies}(\LambdaTermName{equal}(\alpha,\LambdaAdd\,k\,\ChurchNumeral{3}),
     \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}), \theta) \cdot
    \LambdaTermName{implies}( \theta, \LambdaTermName{equal}( \mu, \ChurchNumeral{1}))).
    \end{aligned}$$
    Products abbreviate nested applications of $\LambdaMul$. Multiply this body by the equality test for the
    prescribed root bit, substitute the accessors just described, and abstract the parameter and row input.
    The resulting closed program $\LambdaTermName{evalRow}_ \zeta$ decides the finite certificate clause with root
    bit $\zeta$.
-/
theorem decidable_finiteCertificateClause {ε : ℕ → ℕ} {C : AlphaTerm}
    (c : BorelExpression) (hc : LambdaRelative.Computes ε C c) (b : Bool) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × FinitePrefixPair => finiteCertificateClause c b z.1 z.2) := by
  have hi := projection_computes true
  have hs := (projection_computes true).comp hi
  have ht := rowChild_computes.comp hi
  have hk := (projection_computes false).comp hi
  have hx := (projection_computes true).comp (projection_computes false)
  have hq := (projection_computes false).comp (projection_computes false)
  have hread := fun {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) =>
    listGet_computes.comp (hq.pair hf)
  have hrs := hread hs
  have hrt := hread ht
  have hr0 := hread (numericalConstant_computes 0)
  have hcode : LambdaRelative.Computes ε C (fun n : ℕ => c (NatListCode.decode n)) :=
    ⟨hc.1,fun n => by simpa [Encodable.encode] using hc.2 (NatListCode.decode n)⟩
  have hleafnum := relative_eq
    (LambdaRelative.ofNumerical (listTake_computes.comp (hx.pair (listLength_computes.comp hk))) ε)
    (LambdaRelative.ofNumerical hk ε)
  have hleaf : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      (NatListCode.decode z.unpair.2.unpair.1).take (rowLeaf z.unpair.1).length = rowLeaf z.unpair.1) := by
    simpa [rowLeaf,← NatListCode.encode_injective.eq_iff] using hleafnum
  have harr := relative_certificateArithmetic (hcode.reindex hs) (hcode.reindex ht)
    (LambdaRelative.ofNumerical ((projection_computes true).comp hrs) ε)
    (LambdaRelative.ofNumerical ((projection_computes true).comp hrt) ε)
    (LambdaRelative.ofNumerical ((projection_computes false).comp hrs) ε)
    (LambdaRelative.ofNumerical hk ε) hleaf
  have hroot := relative_eq (LambdaRelative.ofNumerical ((projection_computes true).comp hr0) ε)
    (LambdaRelative.ofNumerical (numericalConstant_computes (if b then 1 else 0)) ε)
  have h := (hroot.and harr).precompNumerical (g := fun z : ℕ × FinitePrefixPair =>
    Nat.pair z.1 (Nat.pair (NatListCode.encode z.2.1) (NatListCode.encode z.2.2)))
    numericalIdentity_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  simpa [finiteCertificateClause,rowWord,rowChild,rowLeaf,NatListCode.encode] using h

private theorem prefix_getD (x : ℕ → ℕ) {i n : ℕ} (hi : i < n) :
    (seqPrefix x n).getD i 0 = x i := by
  simp [seqPrefix, hi, List.getD_eq_getElem?_getD]

private theorem prefix_eq_iff_mem (x : ℕ → ℕ) (s : List ℕ) :
    seqPrefix x s.length = s ↔ x ∈ cyl s := by
  refine ⟨?_, seqPrefix_eq_of_mem_cyl⟩
  intro h
  rw [← h]
  exact mem_cyl_seqPrefix x s.length

/-- Every inspected coordinate lies inside the computable prefix bound. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let a witness $w\in\BaireSpace$ store the pair of a truth bit $u_s$ and a selected child number $j_s$ at
    coordinate $\LambdaListCode{s}$. Require $u_s\le1$ at every word. For every word $s$ and number $k$,
    put $t=s\concat(k)$ and impose the following clauses:
    $$\begin{aligned}
    c(s)=0&\ \Longrightarrow\ u_s=0,\\
    c(s)=1\ \land\ u_s=1\ \land\ j_s=k&\ \Longrightarrow\ c(t)\ne0\ \land\ u_t=1,\\
    c(s)=1\ \land\ c(t)\ne0\ \land\ u_t=1&\ \Longrightarrow\ u_s=1,\\
    c(s)=2\ \land\ c(t)\ne0&\ \Longrightarrow\ u_s+u_t=1,\\
    c(s)=k+3&\ \Longrightarrow\ (u_s=1\ \Longleftrightarrow\ x\in U_k).
    \end{aligned}$$
    The selected child supplies the existential witness at a true union node. Thus these local clauses are
    exactly the truth-assignment rules, with the additional selected-child data. For a valid expression,
    well-founded induction gives the unique truth assignment. Choose a true child at each true union node
    to obtain a certificate, and assign zero to absent nodes. A certificate with root bit one exists exactly
    when $x\in A_c$; a certificate with root bit zero exists exactly when $x\notin A_c$.

    Number the rows by $i=\NatPair{\LambdaListCode{s}}{k}$, and set
    $$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
    The row reads the witness at the codes of $s,t$ and the root, and reads $x$ only through its prefix of
    length $\Length{\LambdaListDecode{k}}$. Hence the first $b(i)$ entries of $x,w$ suffice, including the prescribed
    root bit. The bound is computed by list concatenation, length, pairing, successor, and maximum.
    The clause tester runs the supplied label program at $s,t$, extracts the witness entries, compares
    the indicated prefix with $\LambdaListDecode{k}$, and combines the resulting decision bits.
    The explicit lambda constructions are given in §{sec:lambda-recursive-borel-separation}.

    At length $n$, test each row $i<n$ with $b(i)\le n$, using the prefixes truncated to length $b(i)$.
    Require these tests at every shorter prefix as well, so that the accepted equal-length pairs form a tree.
    Every row is tested once $n\ge\max\{i+1,b(i)\}$. Consequently a branch is exactly a point together with a
    certificate of the prescribed root bit. Projecting the two trees gives $A_c$ and its complement.
    These programs decide finite certificate tests; validity is a hypothesis of the conclusion, and the
    construction does not decide validity or membership in $A_c$ from $x$.
    \end{proof}
-/
theorem finiteCertificateClause_prefix (c : BorelExpression) (b : Bool)
    (x q : ℕ → ℕ) (i : ℕ) :
    finiteCertificateClause c b i
      (seqPrefix x (certificatePrefixBound i), seqPrefix q (certificatePrefixBound i)) ↔
      witnessBit q [] = (if b then 1 else 0) ∧ c.NatClause x q (rowWord i) i.unpair.2 := by
  have hs : NatListCode.encode (rowWord i) < certificatePrefixBound i := by
    unfold certificatePrefixBound
    omega
  have ht : NatListCode.encode (rowChild i) < certificatePrefixBound i := by
    unfold certificatePrefixBound
    omega
  have hr : NatListCode.encode ([] : List ℕ) < certificatePrefixBound i := by
    unfold certificatePrefixBound
    omega
  have hl : (rowLeaf i).length ≤ certificatePrefixBound i := by
    unfold certificatePrefixBound
    omega
  simp only [finiteCertificateClause, prefix_getD q hr, prefix_getD q hs,
    prefix_getD q ht, seqPrefix_take_of_le x hl, prefix_eq_iff_mem]
  rfl

/-- The bounded finite tests are exactly the natural-number certificate. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let a witness $w\in\BaireSpace$ store the pair of a truth bit $u_s$ and a selected child number $j_s$ at
    coordinate $\LambdaListCode{s}$. Require $u_s\le1$ at every word. For every word $s$ and number $k$,
    put $t=s\concat(k)$ and impose the following clauses:
    $$\begin{aligned}
    c(s)=0&\ \Longrightarrow\ u_s=0,\\
    c(s)=1\ \land\ u_s=1\ \land\ j_s=k&\ \Longrightarrow\ c(t)\ne0\ \land\ u_t=1,\\
    c(s)=1\ \land\ c(t)\ne0\ \land\ u_t=1&\ \Longrightarrow\ u_s=1,\\
    c(s)=2\ \land\ c(t)\ne0&\ \Longrightarrow\ u_s+u_t=1,\\
    c(s)=k+3&\ \Longrightarrow\ (u_s=1\ \Longleftrightarrow\ x\in U_k).
    \end{aligned}$$
    The selected child supplies the existential witness at a true union node. Thus these local clauses are
    exactly the truth-assignment rules, with the additional selected-child data. For a valid expression,
    well-founded induction gives the unique truth assignment. Choose a true child at each true union node
    to obtain a certificate, and assign zero to absent nodes. A certificate with root bit one exists exactly
    when $x\in A_c$; a certificate with root bit zero exists exactly when $x\notin A_c$.

    Number the rows by $i=\NatPair{\LambdaListCode{s}}{k}$, and set
    $$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
    The row reads the witness at the codes of $s,t$ and the root, and reads $x$ only through its prefix of
    length $\Length{\LambdaListDecode{k}}$. Hence the first $b(i)$ entries of $x,w$ suffice, including the prescribed
    root bit. The bound is computed by list concatenation, length, pairing, successor, and maximum.
    The clause tester runs the supplied label program at $s,t$, extracts the witness entries, compares
    the indicated prefix with $\LambdaListDecode{k}$, and combines the resulting decision bits.
    The explicit lambda constructions are given in §{sec:lambda-recursive-borel-separation}.

    At length $n$, test each row $i<n$ with $b(i)\le n$, using the prefixes truncated to length $b(i)$.
    Require these tests at every shorter prefix as well, so that the accepted equal-length pairs form a tree.
    Every row is tested once $n\ge\max\{i+1,b(i)\}$. Consequently a branch is exactly a point together with a
    certificate of the prescribed root bit. Projecting the two trees gives $A_c$ and its complement.
    These programs decide finite certificate tests; validity is a hypothesis of the conclusion, and the
    construction does not decide validity or membership in $A_c$ from $x$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    A Borel expression can also be evaluated through finite certificates at the fixed parameter.
-/
theorem all_finiteCertificateClauses_iff (c : BorelExpression) (b : Bool)
    (x q : ℕ → ℕ) :
    (∀ i, finiteCertificateClause c b i
      (seqPrefix x (certificatePrefixBound i), seqPrefix q (certificatePrefixBound i))) ↔
      c.NatCertificate x q ∧ witnessBit q [] = (if b then 1 else 0) := by
  simp only [finiteCertificateClause_prefix]
  constructor
  · intro h
    refine ⟨?_, (h 0).1⟩
    intro s k
    simpa only [rowWord, Nat.unpair_pair, NatListCode.decode_encode] using (h (Nat.pair (NatListCode.encode s) k)).2
  · rintro ⟨h, hr⟩ i
    exact ⟨hr, h (rowWord i) i.unpair.2⟩

/-- Both evaluation sides have lambda-decided tree projections at the fixed
parameter whenever a lambda program computes the external label function. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let a witness $w\in\BaireSpace$ store the pair of a truth bit $u_s$ and a selected child number $j_s$ at
    coordinate $\LambdaListCode{s}$. Require $u_s\le1$ at every word. For every word $s$ and number $k$,
    put $t=s\concat(k)$ and impose the following clauses:
    $$\begin{aligned}
    c(s)=0&\ \Longrightarrow\ u_s=0,\\
    c(s)=1\ \land\ u_s=1\ \land\ j_s=k&\ \Longrightarrow\ c(t)\ne0\ \land\ u_t=1,\\
    c(s)=1\ \land\ c(t)\ne0\ \land\ u_t=1&\ \Longrightarrow\ u_s=1,\\
    c(s)=2\ \land\ c(t)\ne0&\ \Longrightarrow\ u_s+u_t=1,\\
    c(s)=k+3&\ \Longrightarrow\ (u_s=1\ \Longleftrightarrow\ x\in U_k).
    \end{aligned}$$
    The selected child supplies the existential witness at a true union node. Thus these local clauses are
    exactly the truth-assignment rules, with the additional selected-child data. For a valid expression,
    well-founded induction gives the unique truth assignment. Choose a true child at each true union node
    to obtain a certificate, and assign zero to absent nodes. A certificate with root bit one exists exactly
    when $x\in A_c$; a certificate with root bit zero exists exactly when $x\notin A_c$.

    Number the rows by $i=\NatPair{\LambdaListCode{s}}{k}$, and set
    $$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
    The row reads the witness at the codes of $s,t$ and the root, and reads $x$ only through its prefix of
    length $\Length{\LambdaListDecode{k}}$. Hence the first $b(i)$ entries of $x,w$ suffice, including the prescribed
    root bit. The bound is computed by list concatenation, length, pairing, successor, and maximum.
    The clause tester runs the supplied label program at $s,t$, extracts the witness entries, compares
    the indicated prefix with $\LambdaListDecode{k}$, and combines the resulting decision bits.
    The explicit lambda constructions are given in §{sec:lambda-recursive-borel-separation}.

    At length $n$, test each row $i<n$ with $b(i)\le n$, using the prefixes truncated to length $b(i)$.
    Require these tests at every shorter prefix as well, so that the accepted equal-length pairs form a tree.
    Every row is tested once $n\ge\max\{i+1,b(i)\}$. Consequently a branch is exactly a point together with a
    certificate of the prescribed root bit. Projecting the two trees gives $A_c$ and its complement.
    These programs decide finite certificate tests; validity is a hypothesis of the conclusion, and the
    construction does not decide validity or membership in $A_c$ from $x$.
    \end{proof}
-/
theorem projected_evaluationSide {ε : ℕ → ℕ} {C : AlphaTerm}
    (c : BorelExpression) (hc : LambdaRelative.Computes ε C c) (b : Bool) :
    LambdaTree.Projected ε {x | (c, x) ∈ EvaluationSide cylinderBasis b} := by
  have hp := LambdaTree.projected_forall_finitePrefixTests
    (decidable_finiteCertificateClause c hc b) certificatePrefixBound_computes
  have heq : {x | ∃ q, ∀ i, finiteCertificateClause c b i
      (seqPrefix x (certificatePrefixBound i), seqPrefix q (certificatePrefixBound i))} =
      {x | (c, x) ∈ EvaluationSide cylinderBasis b} := by
    ext x
    simp only [mem_ofPred_eq, all_finiteCertificateClauses_iff, natCertificate_root_iff]
  exact heq ▸ hp

/-- A valid lambda-computable Borel expression gives presentations of its
evaluated set and complement at the same parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let a witness $w\in\BaireSpace$ store the pair of a truth bit $u_s$ and a selected child number $j_s$ at
    coordinate $\LambdaListCode{s}$. Require $u_s\le1$ at every word. For every word $s$ and number $k$,
    put $t=s\concat(k)$ and impose the following clauses:
    $$\begin{aligned}
    c(s)=0&\ \Longrightarrow\ u_s=0,\\
    c(s)=1\ \land\ u_s=1\ \land\ j_s=k&\ \Longrightarrow\ c(t)\ne0\ \land\ u_t=1,\\
    c(s)=1\ \land\ c(t)\ne0\ \land\ u_t=1&\ \Longrightarrow\ u_s=1,\\
    c(s)=2\ \land\ c(t)\ne0&\ \Longrightarrow\ u_s+u_t=1,\\
    c(s)=k+3&\ \Longrightarrow\ (u_s=1\ \Longleftrightarrow\ x\in U_k).
    \end{aligned}$$
    The selected child supplies the existential witness at a true union node. Thus these local clauses are
    exactly the truth-assignment rules, with the additional selected-child data. For a valid expression,
    well-founded induction gives the unique truth assignment. Choose a true child at each true union node
    to obtain a certificate, and assign zero to absent nodes. A certificate with root bit one exists exactly
    when $x\in A_c$; a certificate with root bit zero exists exactly when $x\notin A_c$.

    Number the rows by $i=\NatPair{\LambdaListCode{s}}{k}$, and set
    $$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
    The row reads the witness at the codes of $s,t$ and the root, and reads $x$ only through its prefix of
    length $\Length{\LambdaListDecode{k}}$. Hence the first $b(i)$ entries of $x,w$ suffice, including the prescribed
    root bit. The bound is computed by list concatenation, length, pairing, successor, and maximum.
    The clause tester runs the supplied label program at $s,t$, extracts the witness entries, compares
    the indicated prefix with $\LambdaListDecode{k}$, and combines the resulting decision bits.
    The explicit lambda constructions are given in §{sec:lambda-recursive-borel-separation}.

    At length $n$, test each row $i<n$ with $b(i)\le n$, using the prefixes truncated to length $b(i)$.
    Require these tests at every shorter prefix as well, so that the accepted equal-length pairs form a tree.
    Every row is tested once $n\ge\max\{i+1,b(i)\}$. Consequently a branch is exactly a point together with a
    certificate of the prescribed root bit. Projecting the two trees gives $A_c$ and its complement.
    These programs decide finite certificate tests; validity is a hypothesis of the conclusion, and the
    construction does not decide validity or membership in $A_c$ from $x$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Borel evaluation at a fixed parameter
-/
theorem complemented_evaluate {ε : ℕ → ℕ} {C : AlphaTerm}
    (c : BorelExpression) (hc : LambdaRelative.Computes ε C c) (hv : c.Valid) :
    LambdaTree.Complemented ε (c.evaluate hv.2.2.2.2.2 cylinderBasis []) := by
  have ht := projected_evaluationSide c hc true
  have hf := projected_evaluationSide c hc false
  have heq : {x | (c, x) ∈ EvaluationSide cylinderBasis true} =
      c.evaluate hv.2.2.2.2.2 cylinderBasis [] := by
    ext x
    exact evaluationSide_iff_mem cylinderBasis c hv x
  have hfalse : {x | (c, x) ∈ EvaluationSide cylinderBasis false} =
      (c.evaluate hv.2.2.2.2.2 cylinderBasis [])ᶜ := by
    ext x
    have h := evaluationSides_complementary cylinderBasis c hv x
    rw [evaluationSide_iff_mem cylinderBasis c hv x] at h
    simp only [mem_ofPred_eq, mem_compl_iff]
    tauto
  exact ⟨heq ▸ ht, hfalse ▸ hf⟩

end BorelExpression
end PolishSpaceBook
