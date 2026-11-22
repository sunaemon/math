module

public import PolishSpaceBook.ComputableRationalCodes
public import PolishSpaceBook.LambdaNumericalFunctions

@[expose] public section

/-! # Rational arithmetic by closed lambda terms

Nested numerical pairing encodes signed numerators and positive denominators.
Every natural number decodes, so the programs are total on all numeral inputs.
No evaluator for a different programming language is used.
-/
namespace PolishSpaceBook
namespace RationalCode

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\RationalCode{a}{b}{c}:=\NatPair{\NatPair{a}{b}}{c},\qquad
    \RationalCode{a}{b}{c}\longmapsto\frac{a-b}{c+1},\qquad a,b,c\in\NN.$$
    The numerator difference is taken in the integers. Every natural number decodes to exactly one triple, and every
    rational has at least one code. No reduction to lowest terms is required.
-/
def natCode (c : RationalCode) : ℕ := Nat.pair (Nat.pair c.1.1 c.1.2) c.2
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\RationalCode{a}{b}{c}:=\NatPair{\NatPair{a}{b}}{c},\qquad
    \RationalCode{a}{b}{c}\longmapsto\frac{a-b}{c+1},\qquad a,b,c\in\NN.$$
    The numerator difference is taken in the integers. Every natural number decodes to exactly one triple, and every
    rational has at least one code. No reduction to lowest terms is required.
-/
def ofNat (n : ℕ) : RationalCode := ((n.unpair.1.unpair.1, n.unpair.1.unpair.2), n.unpair.2)

@[simp] theorem ofNat_natCode (c : RationalCode) : ofNat (natCode c) = c := by
  rcases c with ⟨⟨a,b⟩,d⟩; simp [ofNat,natCode,Nat.unpair_pair]

@[simp] theorem natCode_ofNat (n : ℕ) : natCode (ofNat n) = n := by
  simp [ofNat,natCode,Nat.pair_unpair]

end RationalCode

namespace NamedLambda.AlphaTerm
open RationalCode

/-- Extract one of the two natural numerator parts. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    First define closed component programs
    $$\begin{aligned}
    P&:=\lambdaab{u}{\LambdaNumericProjection{1}(\LambdaNumericProjection{1}u)},\\
    N&:=\lambdaab{u}{\LambdaNumericProjection{2}(\LambdaNumericProjection{1}u)},\\
    D&:=\lambdaab{u}{\LambdaSucc(\LambdaNumericProjection{2}u)}.
    \end{aligned}$$
    On the numeral for $\RationalCode{a}{b}{c}$ these return the numerals for $a,b,c+1$, respectively. For a numerical input
    term $z$, abbreviate $u:=\LambdaNumericProjection{1}z$ and $v:=\LambdaNumericProjection{2}z$, and use the following
    expressions, whose only possible free variable is $z$:
    $$\begin{aligned}
    A&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Pv)\,(Du)),\\
    B&:=\LambdaAdd\,(\LambdaMul\,(Nu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
    C&:=\LambdaMul\,(Du)\,(Dv),\\
    E&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
    F&:=\LambdaAdd\,(\LambdaMul\,(Pv)\,(Du))\,(\LambdaMul\,(Nu)\,(Dv)).
    \end{aligned}$$
-/
def rationalNumeratorTerm (positive : Bool) : AlphaTerm :=
  numericalCompose (numericalProjectionTerm positive) (numericalProjectionTerm true)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    First define closed component programs
    $$\begin{aligned}
    P&:=\lambdaab{u}{\LambdaNumericProjection{1}(\LambdaNumericProjection{1}u)},\\
    N&:=\lambdaab{u}{\LambdaNumericProjection{2}(\LambdaNumericProjection{1}u)},\\
    D&:=\lambdaab{u}{\LambdaSucc(\LambdaNumericProjection{2}u)}.
    \end{aligned}$$
    On the numeral for $\RationalCode{a}{b}{c}$ these return the numerals for $a,b,c+1$, respectively. For a numerical input
    term $z$, abbreviate $u:=\LambdaNumericProjection{1}z$ and $v:=\LambdaNumericProjection{2}z$, and use the following
    expressions, whose only possible free variable is $z$:
    $$\begin{aligned}
    A&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Pv)\,(Du)),\\
    B&:=\LambdaAdd\,(\LambdaMul\,(Nu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
    C&:=\LambdaMul\,(Du)\,(Dv),\\
    E&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
    F&:=\LambdaAdd\,(\LambdaMul\,(Pv)\,(Du))\,(\LambdaMul\,(Nu)\,(Dv)).
    \end{aligned}$$
-/
def rationalDenominatorTerm : AlphaTerm :=
  numericalCompose successorTerm (numericalProjectionTerm false)

theorem rationalNumerator_computes (positive : Bool) :
    NumericalComputes (rationalNumeratorTerm positive)
      (fun n => if positive then (ofNat n).1.1 else (ofNat n).1.2) := by
  simpa [rationalNumeratorTerm,ofNat] using
    (projection_computes positive).comp (projection_computes true)

theorem rationalDenominator_computes :
    NumericalComputes rationalDenominatorTerm (fun n => (ofNat n).2 + 1) := by
  simpa [rationalDenominatorTerm,ofNat] using successor_computes.comp (projection_computes false)

/-- Feed one component of a paired numerical input to a program. -/
def onComponent (F : AlphaTerm) (first : Bool) : AlphaTerm :=
  numericalCompose F (numericalProjectionTerm first)

theorem NumericalComputes.onComponent {F : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes F f) (first : Bool) :
    NumericalComputes (onComponent F first)
      (fun n => f (if first then n.unpair.1 else n.unpair.2)) :=
  hf.comp (projection_computes first)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    First define closed component programs
    $$\begin{aligned}
    P&:=\lambdaab{u}{\LambdaNumericProjection{1}(\LambdaNumericProjection{1}u)},\\
    N&:=\lambdaab{u}{\LambdaNumericProjection{2}(\LambdaNumericProjection{1}u)},\\
    D&:=\lambdaab{u}{\LambdaSucc(\LambdaNumericProjection{2}u)}.
    \end{aligned}$$
    On the numeral for $\RationalCode{a}{b}{c}$ these return the numerals for $a,b,c+1$, respectively. For a numerical input
    term $z$, abbreviate $u:=\LambdaNumericProjection{1}z$ and $v:=\LambdaNumericProjection{2}z$, and use the following
    expressions, whose only possible free variable is $z$:
    $$\begin{aligned}
    A&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Pv)\,(Du)),\\
    B&:=\LambdaAdd\,(\LambdaMul\,(Nu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
    C&:=\LambdaMul\,(Du)\,(Dv),\\
    E&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
    F&:=\LambdaAdd\,(\LambdaMul\,(Pv)\,(Du))\,(\LambdaMul\,(Nu)\,(Dv)).
    \end{aligned}$$
-/
def rationalCrossTerm (positive first : Bool) : AlphaTerm :=
  mulNumerical (onComponent (rationalNumeratorTerm positive) first)
    (onComponent rationalDenominatorTerm (!first))

theorem rationalCross_computes (positive first : Bool) :
    NumericalComputes (rationalCrossTerm positive first)
      (fun n => (if positive then (ofNat (if first then n.unpair.1 else n.unpair.2)).1.1
        else (ofNat (if first then n.unpair.1 else n.unpair.2)).1.2) *
        ((ofNat (if !first then n.unpair.1 else n.unpair.2)).2 + 1)) :=
  ((rationalNumerator_computes positive).onComponent first).mul
    (rationalDenominator_computes.onComponent (!first))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define
    $$\begin{aligned}
    \LambdaRationalAdd&:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericPair\,A\,B)\,(\LambdaPred\,C)},\\
    \LambdaRationalLess&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,E}{F}{\ChurchNumeral{1}}{\ChurchNumeral{0}}},\\
    \LambdaDyadic&:=\lambdaab{n}{\LambdaNumericPair\,\ChurchNumeral{\NatPair{1}{0}}\,
     (\LambdaPred\,(n\,(\LambdaMul\,\ChurchNumeral{2})\,\ChurchNumeral{1}))}.
    \end{aligned}$$
    Expand the abbreviations before abstraction, using fresh bound variables inside the component terms. Each displayed
    program is a single closed lambda term.
-/
def rationalAddTerm : AlphaTerm :=
  pairNumerical
    (pairNumerical
      (addNumerical (rationalCrossTerm true true) (rationalCrossTerm true false))
      (addNumerical (rationalCrossTerm false true) (rationalCrossTerm false false)))
    (numericalCompose predecessorTerm
      (mulNumerical (onComponent rationalDenominatorTerm true)
        (onComponent rationalDenominatorTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda reductions for rational codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    After the outer abstraction of the addition program is contracted, numerical projections recover the six input entries. Reduction in application contexts gives $A\to_\beta^*\ChurchNumeral{ae+ud}$, $B\to_\beta^*\ChurchNumeral{be+vd}$, and $C\to_\beta^*\ChurchNumeral{de}$. Predecessor and two numerical pairings give the asserted output. Its value is
    $$\frac{ae+ud-be-vd}{de}=\frac{a-b}{d}+\frac{u-v}{e}.$$
    For comparison the same argument gives the cross sums $ae+vd$ and $ud+be$. Successor followed by the less-than-or-equal test returns one exactly for strict inequality. Multiplication by the positive number $de$ shows that this is equivalent to $(a-b)/d<(u-v)/e$.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The preceding beta-reductions provide the three closed programs and their outputs on every numerical input.
    Their rational values and the comparison criterion were verified in the same proof.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Use the rational codes of §{sec:lambda-rational-arithmetic}, whose decoded values are $(a-b)/(c+1)$ for $a,b,c\in\NN$.
    Addition, strict comparison, and the program producing $2^{-k}$ terminate on every numerical input. Rational lists store
    polynomial coefficients and finite approximations; dyadic codes supply error bounds in the metric searches below.
-/
theorem rationalAdd_computes : NumericalComputes rationalAddTerm
    (fun n => natCode (RationalCode.add (ofNat n.unpair.1) (ofNat n.unpair.2))) := by
  have hp := (rationalCross_computes true true).add (rationalCross_computes true false)
  have hn := (rationalCross_computes false true).add (rationalCross_computes false false)
  have hd := predecessor_computes.comp
    ((rationalDenominator_computes.onComponent true).mul
      (rationalDenominator_computes.onComponent false))
  simpa [rationalAddTerm,RationalCode.add,natCode] using (hp.pair hn).pair hd

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define
    $$\begin{aligned}
    \LambdaRationalAdd&:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericPair\,A\,B)\,(\LambdaPred\,C)},\\
    \LambdaRationalLess&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,E}{F}{\ChurchNumeral{1}}{\ChurchNumeral{0}}},\\
    \LambdaDyadic&:=\lambdaab{n}{\LambdaNumericPair\,\ChurchNumeral{\NatPair{1}{0}}\,
     (\LambdaPred\,(n\,(\LambdaMul\,\ChurchNumeral{2})\,\ChurchNumeral{1}))}.
    \end{aligned}$$
    Expand the abbreviations before abstraction, using fresh bound variables inside the component terms. Each displayed
    program is a single closed lambda term.
-/
def rationalLessTerm : AlphaTerm :=
  numericalCombine strictLessTerm
    (addNumerical (rationalCrossTerm true true) (rationalCrossTerm false false))
    (addNumerical (rationalCrossTerm true false) (rationalCrossTerm false true))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda reductions for rational codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The preceding beta-reductions provide the three closed programs and their outputs on every numerical input.
    Their rational values and the comparison criterion were verified in the same proof.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Use the rational codes of §{sec:lambda-rational-arithmetic}, whose decoded values are $(a-b)/(c+1)$ for $a,b,c\in\NN$.
    Addition, strict comparison, and the program producing $2^{-k}$ terminate on every numerical input. Rational lists store
    polynomial coefficients and finite approximations; dyadic codes supply error bounds in the metric searches below.
-/
theorem rationalLess_computes : NumericalComputes rationalLessTerm
    (fun n => if (ofNat n.unpair.1).value < (ofNat n.unpair.2).value then 1 else 0) := by
  have h := ((rationalCross_computes true true).add (rationalCross_computes false false)).combine
    ((rationalCross_computes true false).add (rationalCross_computes false true))
    strictLessTerm_closed (fun a b => if a < b then 1 else 0) strictLessTerm_apply
  simpa [rationalLessTerm,← RationalCode.lt_iff,RationalCode.lt] using h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define
    $$\begin{aligned}
    \LambdaRationalAdd&:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericPair\,A\,B)\,(\LambdaPred\,C)},\\
    \LambdaRationalLess&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,E}{F}{\ChurchNumeral{1}}{\ChurchNumeral{0}}},\\
    \LambdaDyadic&:=\lambdaab{n}{\LambdaNumericPair\,\ChurchNumeral{\NatPair{1}{0}}\,
     (\LambdaPred\,(n\,(\LambdaMul\,\ChurchNumeral{2})\,\ChurchNumeral{1}))}.
    \end{aligned}$$
    Expand the abbreviations before abstraction, using fresh bound variables inside the component terms. Each displayed
    program is a single closed lambda term.
-/
def rationalDyadicTerm : AlphaTerm :=
  pairNumerical (numericalConstant (Nat.pair 1 0))
    (numericalCompose predecessorTerm powerTwoTerm)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda reductions for rational codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The preceding beta-reductions provide the three closed programs and their outputs on every numerical input.
    Their rational values and the comparison criterion were verified in the same proof.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Rational arithmetic by lambda terms
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Use the rational codes of §{sec:lambda-rational-arithmetic}, whose decoded values are $(a-b)/(c+1)$ for $a,b,c\in\NN$.
    Addition, strict comparison, and the program producing $2^{-k}$ terminate on every numerical input. Rational lists store
    polynomial coefficients and finite approximations; dyadic codes supply error bounds in the metric searches below.
-/
theorem rationalDyadic_computes : NumericalComputes rationalDyadicTerm
    (fun n => natCode (dyadic n)) := by
  simpa [rationalDyadicTerm,natCode,dyadic] using
    (numericalConstant_computes (Nat.pair 1 0)).pair (predecessor_computes.comp powerTwo_computes)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Rational arithmetic by lambda terms
-/
theorem rationalAdd_apply (a b : RationalCode) :
    Relation.ReflTransGen Beta (app rationalAddTerm (numeral (Nat.pair (natCode a) (natCode b))))
      (numeral (natCode (RationalCode.add a b))) := by
  simpa [Nat.unpair_pair] using rationalAdd_computes.2 (Nat.pair (natCode a) (natCode b))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Rational arithmetic by lambda terms
-/
theorem rationalLess_apply (a b : RationalCode) :
    Relation.ReflTransGen Beta (app rationalLessTerm (numeral (Nat.pair (natCode a) (natCode b))))
      (numeral (if a.value < b.value then 1 else 0)) := by
  simpa [Nat.unpair_pair] using rationalLess_computes.2 (Nat.pair (natCode a) (natCode b))

/-- The computed sum has the required mathematical value, also for noncanonical codes. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    After the outer abstraction of the addition program is contracted, numerical projections recover the six input entries. Reduction in application contexts gives $A\to_\beta^*\ChurchNumeral{ae+ud}$, $B\to_\beta^*\ChurchNumeral{be+vd}$, and $C\to_\beta^*\ChurchNumeral{de}$. Predecessor and two numerical pairings give the asserted output. Its value is
    $$\frac{ae+ud-be-vd}{de}=\frac{a-b}{d}+\frac{u-v}{e}.$$
    For comparison the same argument gives the cross sums $ae+vd$ and $ud+be$. Successor followed by the less-than-or-equal test returns one exactly for strict inequality. Multiplication by the positive number $de$ shows that this is equivalent to $(a-b)/d<(u-v)/e$.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The preceding beta-reductions provide the three closed programs and their outputs on every numerical input.
    Their rational values and the comparison criterion were verified in the same proof.
    \end{proof}
-/
theorem rationalAdd_value (n : ℕ) :
    (ofNat (natCode (RationalCode.add (ofNat n.unpair.1) (ofNat n.unpair.2)))).value =
      (ofNat n.unpair.1).value + (ofNat n.unpair.2).value := by simp

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the dyadic program, induction on $k$ shows that applying $\ChurchNumeral{k}$ to multiplication by two and then to $\ChurchNumeral{1}$ reduces to $\ChurchNumeral{2^k}$. The successor step uses one further multiplication, so this is ordinary Church iteration. Predecessor and pairing finish the reduction. Its denominator is exactly $2^k$, so its value is $2^{-k}$. Every natural input decodes, every component reduction is finite, and all remaining variables are bound. This proves totality and closedness, including the zero inputs. Confluence gives uniqueness of each numeral output.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The preceding beta-reductions provide the three closed programs and their outputs on every numerical input.
    Their rational values and the comparison criterion were verified in the same proof.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Rational arithmetic by lambda terms
-/
theorem rationalDyadic_value (n : ℕ) :
    (ofNat (natCode (dyadic n))).value = (1/2 : ℚ)^n := by simp

end NamedLambda.AlphaTerm
end PolishSpaceBook
