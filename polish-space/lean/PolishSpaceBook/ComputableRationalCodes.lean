module

public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# Effective rational data for metric algorithms

A code `((a,b),d)` denotes `(a-b)/(d+1)`. Noncanonical codes avoid any
normalization step; the denoted objects are mathlib rationals. Addition,
strict comparison, and dyadic error bounds have primitive-recursive codes.
-/

namespace PolishSpaceBook

abbrev RationalCode := (ℕ × ℕ) × ℕ

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
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{RationalValue,LambdaBallTest,LambdaBallSemidecider}
    \end{mathmeta}
    We construct the numerical test used for rational balls. The construction itself needs no metric space. For a rational
    code $c=\RationalCode{a}{b}{d}$, write $\RationalValue{c}:=(a-b)/(d+1)$. Let $A:\NN^3\to\NN$ be a total function whose
    outputs are rational codes, and suppose one closed term $M$ satisfies
    $$M\,\ChurchNumeral{\NatPair{i}{\NatPair{j}{n}}}\to_\beta^*\ChurchNumeral{A(i,j,n)}$$
    for all $i,j,n$. Given an input name $p$, a center index $i$, a radius code $c$, and a stage $n$, the desired test is
    $$\RationalValue{A(p(n),i,n)}+2\cdot2^{-n}<\RationalValue{c}.$$
    It uses only a query to $p$, the supplied program $M$, and the arithmetic of §{sec:lambda-rational-arithmetic}.
-/
def value (c : RationalCode) : ℚ :=
  ((c.1.1 : ℚ) - c.1.2) / ((c.2 + 1 : ℕ) : ℚ)

/-@ legacy-booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To implement the metric searches, use the approximation form of the distance data. Fix a total computable rational-valued function $A$ such that
    $$
    |A(i,j,k)-d(q_i,q_j)|\le 2^{-k}.
    $$
    The same algorithm must work for all $i,j,k$. For concrete rational arithmetic, a triple $(a,b,c)\in\NN^3$ can code $(a-b)/(c+1)$. Every rational has such a code; repeated codes cause no difficulty. Addition and strict comparison are primitive recursive on these codes by cross-multiplication, since denominators are positive. The code for $2^{-k}$ is obtained primitively recursively from $k$.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Numerical unpairing recovers the three entries from every natural number. Conversely, a rational with integer
    numerator $z$ and positive denominator $d$ has such a code: write $z=a-b$ with $a,b\in\NN$ and take $c=d-1$.
-/
theorem value_surjective : Function.Surjective value := by
  intro r
  refine ⟨((r.num.toNat, (-r.num).toNat), r.den - 1), ?_⟩
  have hd : r.den - 1 + 1 = r.den := Nat.sub_add_cancel r.den_pos
  have hn : (r.num.toNat : ℚ) - ((-r.num).toNat : ℚ) = r.num := by
    have hi : (r.num.toNat : ℤ) - ((-r.num).toNat : ℤ) = r.num := by omega
    exact_mod_cast hi
  simpa only [value, hd, hn] using r.num_div_den

def add (a b : RationalCode) : RationalCode :=
  ((a.1.1 * (b.2 + 1) + b.1.1 * (a.2 + 1),
    a.1.2 * (b.2 + 1) + b.1.2 * (a.2 + 1)), (a.2 + 1) * (b.2 + 1) - 1)

def lt (a b : RationalCode) : Prop :=
  a.1.1 * (b.2 + 1) + b.1.2 * (a.2 + 1) <
    b.1.1 * (a.2 + 1) + a.1.2 * (b.2 + 1)

instance (a b : RationalCode) : Decidable (lt a b) := inferInstanceAs (Decidable (_ < _))

def dyadic (n : ℕ) : RationalCode := ((1, 0), 2 ^ n - 1)

@[simp] theorem value_add (a b : RationalCode) : value (add a b) = value a + value b := by
  have hd : (a.2 + 1) * (b.2 + 1) - 1 + 1 = (a.2 + 1) * (b.2 + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  simp only [value, add, hd, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem lt_iff (a b : RationalCode) : lt a b ↔ value a < value b := by
  unfold value
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have he : lt a b ↔ (a.1.1 : ℚ) * (b.2 + 1) + b.1.2 * (a.2 + 1) <
      b.1.1 * (a.2 + 1) + a.1.2 * (b.2 + 1) := by
    unfold lt
    exact_mod_cast Iff.rfl
  rw [he]
  push_cast
  constructor <;> intro h <;> nlinarith

@[simp] theorem value_dyadic (n : ℕ) : value (dyadic n) = (1 / 2 : ℚ) ^ n := by
  have hd : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  simp [value, dyadic, hd]

@[simp] theorem real_value_dyadic (n : ℕ) : (value (dyadic n) : ℝ) = (1 / 2 : ℝ) ^ n := by
  simp

/-@ legacy-booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To implement the metric searches, use the approximation form of the distance data. Fix a total computable rational-valued function $A$ such that
    $$
    |A(i,j,k)-d(q_i,q_j)|\le 2^{-k}.
    $$
    The same algorithm must work for all $i,j,k$. For concrete rational arithmetic, a triple $(a,b,c)\in\NN^3$ can code $(a-b)/(c+1)$. Every rational has such a code; repeated codes cause no difficulty. Addition and strict comparison are primitive recursive on these codes by cross-multiplication, since denominators are positive. The code for $2^{-k}$ is obtained primitively recursively from $k$.
-/
theorem primrec_add : Primrec₂ add := by
  have ap : Primrec (fun z : RationalCode × RationalCode => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have an : Primrec (fun z : RationalCode × RationalCode => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ad : Primrec (fun z : RationalCode × RationalCode => z.1.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun z : RationalCode × RationalCode => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have bn : Primrec (fun z : RationalCode × RationalCode => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have bd : Primrec (fun z : RationalCode × RationalCode => z.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bd) (Primrec.nat_mul.comp bp ad)).pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp an bd) (Primrec.nat_mul.comp bn ad))).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp ad bd) (Primrec.const 1))

/-@ legacy-booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To implement the metric searches, use the approximation form of the distance data. Fix a total computable rational-valued function $A$ such that
    $$
    |A(i,j,k)-d(q_i,q_j)|\le 2^{-k}.
    $$
    The same algorithm must work for all $i,j,k$. For concrete rational arithmetic, a triple $(a,b,c)\in\NN^3$ can code $(a-b)/(c+1)$. Every rational has such a code; repeated codes cause no difficulty. Addition and strict comparison are primitive recursive on these codes by cross-multiplication, since denominators are positive. The code for $2^{-k}$ is obtained primitively recursively from $k$.
-/
theorem primrec_lt : PrimrecRel lt := by
  have ap : Primrec (fun z : RationalCode × RationalCode => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have an : Primrec (fun z : RationalCode × RationalCode => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ad : Primrec (fun z : RationalCode × RationalCode => z.1.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun z : RationalCode × RationalCode => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have bn : Primrec (fun z : RationalCode × RationalCode => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have bd : Primrec (fun z : RationalCode × RationalCode => z.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp ap bd) (Primrec.nat_mul.comp bn ad))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp bp ad) (Primrec.nat_mul.comp an bd))

/-@ legacy-booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To implement the metric searches, use the approximation form of the distance data. Fix a total computable rational-valued function $A$ such that
    $$
    |A(i,j,k)-d(q_i,q_j)|\le 2^{-k}.
    $$
    The same algorithm must work for all $i,j,k$. For concrete rational arithmetic, a triple $(a,b,c)\in\NN^3$ can code $(a-b)/(c+1)$. Every rational has such a code; repeated codes cause no difficulty. Addition and strict comparison are primitive recursive on these codes by cross-multiplication, since denominators are positive. The code for $2^{-k}$ is obtained primitively recursively from $k$.
-/
theorem primrec_dyadic : Primrec dyadic :=
  ((Primrec.const 1).pair (Primrec.const 0)).pair
    (Primrec.nat_sub.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id) (Primrec.const 1))

end RationalCode
end PolishSpaceBook
