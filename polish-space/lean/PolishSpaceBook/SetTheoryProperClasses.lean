module

public import PolishSpaceBook.SetTheoryBasicAbbreviations
public import PolishSpaceBook.SetTheoryOrdinalFormulas

@[expose] public section

/-! # The universe and the ordinals cannot be collected into sets -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas
universe u

namespace AbstractMembership
variable {S : Type u} [membershipLanguage.Structure S]

/-- Class notation denotes the predicate of a formula, not an extra object of the model. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefineas{class in set theory}{class} is a collection of sets defined by a formula, $\{x : \varphi(x)\}$. A
    \termdefine{class function} is a definable functional relation: a formula $\Phi(x,y)$ such that, for each set $x$ in the
    intended domain class, there is a unique set $y$ with $\Phi(x,y)$. We write $F(x)=y$ for this unique value, but this is
    still only shorthand for the defining formula. A class that is itself an element of the universe is a
    \termdefineas{set in ZFC}{set}; one that is not is a \termdefine{proper class}. Standard examples of proper classes:
-/
def DefinableClass (φ : ForcingFormulas.Formula 1) : Set S :=
  fun x => φ.Realize Empty.elim ![x]

/-- A class is a set precisely when an internal object has exactly its members. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefineas{class in set theory}{class} is a collection of sets defined by a formula, $\{x : \varphi(x)\}$. A
    \termdefine{class function} is a definable functional relation: a formula $\Phi(x,y)$ such that, for each set $x$ in the
    intended domain class, there is a unique set $y$ with $\Phi(x,y)$. We write $F(x)=y$ for this unique value, but this is
    still only shorthand for the defining formula. A class that is itself an element of the universe is a
    \termdefineas{set in ZFC}{set}; one that is not is a \termdefine{proper class}. Standard examples of proper classes:
-/
def ClassIsSet (C : Set S) : Prop :=
  ∃ a : S, ∀ x : S, member x a ↔ x ∈ C

/-- Proper classes are predicates not represented by an internal set. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefineas{class in set theory}{class} is a collection of sets defined by a formula, $\{x : \varphi(x)\}$. A
    \termdefine{class function} is a definable functional relation: a formula $\Phi(x,y)$ such that, for each set $x$ in the
    intended domain class, there is a unique set $y$ with $\Phi(x,y)$. We write $F(x)=y$ for this unique value, but this is
    still only shorthand for the defining formula. A class that is itself an element of the universe is a
    \termdefineas{set in ZFC}{set}; one that is not is a \termdefine{proper class}. Standard examples of proper classes:
-/
def ClassIsProper (C : Set S) : Prop := ¬ClassIsSet C

/-- A class function is a definable relation with one value at every intended input. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefineas{class in set theory}{class} is a collection of sets defined by a formula, $\{x : \varphi(x)\}$. A
    \termdefine{class function} is a definable functional relation: a formula $\Phi(x,y)$ such that, for each set $x$ in the
    intended domain class, there is a unique set $y$ with $\Phi(x,y)$. We write $F(x)=y$ for this unique value, but this is
    still only shorthand for the defining formula. A class that is itself an element of the universe is a
    \termdefineas{set in ZFC}{set}; one that is not is a \termdefine{proper class}. Standard examples of proper classes:
-/
def IsDefinableClassFunction (domain : Set S) (φ : ForcingFormulas.Formula 2) : Prop :=
  ∀ a : S, a ∈ domain → ∃! b : S, φ.Realize Empty.elim ![a, b]

end AbstractMembership

/-- Burali–Forti: a set consisting of exactly all ordinals would itself be an ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    That $V$ and $\mathrm{Ord}$ are not sets is the \termdefine{Russell paradox} and \termdefine{Burali-Forti paradox}
    respectively.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $V := \{x : x = x\}$, the universe of all sets.
    *   $\mathrm{Ord} := \{x : \mathrm{Ord}(x)\}$, the class of ordinals.
    *   $\mathrm{Card}$, the class of cardinals.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
theorem no_set_of_all_ordinals :
    ¬ ∃ v : ZFSet.{u}, ∀ x : ZFSet.{u}, x ∈ v ↔ x.IsOrdinal := by
  rintro ⟨v, hv⟩
  have hvo : v.IsOrdinal := by
    apply ZFSet.isOrdinal_iff_forall_mem_isTransitive.mpr
    constructor
    · intro x hx y hy
      exact (hv y).mpr (((hv x).mp hx).mem hy)
    · intro x hx
      exact ((hv x).mp hx).isTransitive
  exact ZFSet.mem_irrefl v ((hv v).mpr hvo)

/-- Even the initial ordinals representing cardinals cannot all belong to one set. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $V := \{x : x = x\}$, the universe of all sets.
    *   $\mathrm{Ord} := \{x : \mathrm{Ord}(x)\}$, the class of ordinals.
    *   $\mathrm{Card}$, the class of cardinals.
-/
theorem no_set_contains_all_cardinalOrdinals :
    ¬ ∃ v : ZFSet.{u}, ∀ c : Cardinal.{u}, c.ord.toZFSet ∈ v := by
  rintro ⟨v, hv⟩
  have hmem := hv (Order.succ v.rank.card)
  have hlt := ZFSet.rank_lt_of_mem hmem
  rw [Ordinal.rank_toZFSet] at hlt
  exact (not_lt_of_ge (Cardinal.lt_ord_succ_card v.rank).le) hlt

end PolishSpaceBook.SetTheoryModels
