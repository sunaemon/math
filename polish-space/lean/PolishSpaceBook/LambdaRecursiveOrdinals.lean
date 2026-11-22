module

public import PolishSpaceBook.LambdaRelativeIndices
public import PolishSpaceBook.LambdaPureParameters
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-! # Relative recursive ordinals on decidable numerical domains

The well-order is the canonical `IsWellOrder` on a subtype of natural
numbers. Both domain membership and comparison have actual lambda deciders
at one fixed parameter. Well-foundedness is an external hypothesis, not a
property decided by these programs.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A presentation at a fixed parameter $\varepsilon$ consists of total closed decision programs $D,R$ for a
    subset of $\NN$ and a relation on $\NN$, whose restriction to that subset is a strict well order. The
    program $R$ receives a numerical pair. This is the presentation used in §{sec:hyperarithmetic-hierarchy}.
    Its well-foundedness is an external assumption. The operations below preserve that assumption; they do
    not test it.
    For numerical terms $X,Y$, abbreviate
    $$\begin{aligned}
    N(X)&:=\LambdaZeroTest\,X\,\ChurchNumeral{1}\,\ChurchNumeral{0},\\
    U(X,Y)&:=N(\LambdaMul\,(N(X))\,(N(Y))).
    \end{aligned}$$
    On decision bits these compute negation and disjunction. Write $p_i:=\LambdaNumericProjection{i}$.
-/
theorem decidablePredicate_or_for_ordinals {ε : ℕ → ℕ} {α : Type} [Encodable α] {R S : α → Prop}
    (hR : DecidablePredicate ε R) (hS : DecidablePredicate ε S) :
    DecidablePredicate ε (fun a => R a ∨ S a) := by
  classical
  simpa only [not_and_or,not_not] using (hR.not.and hS.not).not

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A presentation at a fixed parameter $\varepsilon$ consists of total closed decision programs $D,R$ for a
    subset of $\NN$ and a relation on $\NN$, whose restriction to that subset is a strict well order. The
    program $R$ receives a numerical pair. This is the presentation used in §{sec:hyperarithmetic-hierarchy}.
    Its well-foundedness is an external assumption. The operations below preserve that assumption; they do
    not test it.
    For numerical terms $X,Y$, abbreviate
    $$\begin{aligned}
    N(X)&:=\LambdaZeroTest\,X\,\ChurchNumeral{1}\,\ChurchNumeral{0},\\
    U(X,Y)&:=N(\LambdaMul\,(N(X))\,(N(Y))).
    \end{aligned}$$
    On decision bits these compute negation and disjunction. Write $p_i:=\LambdaNumericProjection{i}$.
-/
theorem decidable_zero (ε : ℕ → ℕ) : DecidablePredicate ε (fun n : ℕ => n = 0) := by
  refine ⟨_,reverseZero_computes.uniform.1,fun n => ⟨?_,?_⟩⟩ <;> intro hn <;>
    simpa [hn] using reverseZero_computes.uniform.2 ε n

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    **Recursive ordinals.** A \termdefine{recursive ordinal} is the order type of a computable linear order on a
    computable subset of $\NN$ that is externally well founded. More generally, a presentation relative to
    $\varepsilon$ consists of a domain $D\IncludedIn\NN$ and a relation $R$ on $\NN$, with total lambda
    membership and comparison programs at $\varepsilon$, such that the restriction of $R$ to $D$ is a strict
    well order. No requirement is placed on comparisons outside $D$. Well-foundedness is a hypothesis about
    the presentation, not a property these programs must decide.
    Write $\relativeChurchKleeneOrd{\varepsilon}$ for the supremum of the order types of these presentations.
    For the constant-zero parameter this is the \termdefineas{Church--Kleene ordinal}{Church--Kleene ordinal}
    $\churchKleeneOrd$. Substituting a closed implementation of the zero function eliminates the parameter,
    as proved in §{sec:lambda-recursive-order-programs}.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A presentation at a fixed parameter $\varepsilon$ consists of total closed decision programs $D,R$ for a
    subset of $\NN$ and a relation on $\NN$, whose restriction to that subset is a strict well order. The
    program $R$ receives a numerical pair. This is the presentation used in §{sec:hyperarithmetic-hierarchy}.
    Its well-foundedness is an external assumption. The operations below preserve that assumption; they do
    not test it.
    For numerical terms $X,Y$, abbreviate
    $$\begin{aligned}
    N(X)&:=\LambdaZeroTest\,X\,\ChurchNumeral{1}\,\ChurchNumeral{0},\\
    U(X,Y)&:=N(\LambdaMul\,(N(X))\,(N(Y))).
    \end{aligned}$$
    On decision bits these compute negation and disjunction. Write $p_i:=\LambdaNumericProjection{i}$.
-/
structure WellOrderPresentation (ε : ℕ → ℕ) where
  domain : ℕ → Prop
  relation : ℕ → ℕ → Prop
  domain_decidable : DecidablePredicate ε domain
  relation_decidable : DecidablePredicate ε (fun z : ℕ × ℕ => relation z.1 z.2)
  wellOrder : IsWellOrder {n // domain n} (fun a b => relation a.val b.val)

namespace WellOrderPresentation
variable {ε : ℕ → ℕ}
abbrev Carrier (W : WellOrderPresentation ε) := {n // W.domain n}
abbrev order (W : WellOrderPresentation ε) : W.Carrier → W.Carrier → Prop :=
  fun a b => W.relation a.val b.val
instance (W : WellOrderPresentation ε) : IsWellOrder W.Carrier W.order := W.wellOrder

noncomputable def orderType (W : WellOrderPresentation ε) : Ordinal := Ordinal.type W.order

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For an element with code $a$ in the original domain, the initial-segment membership program is
    $$D_{<a}:=\lambdaab{o}{\lambdaab{n}{\LambdaMul\,(Do\,n)\,
     (Ro(\LambdaNumericPair\,n\,\ChurchNumeral{a}))}}.$$
    Its comparison program remains $R$. For the successor, zero codes the new largest element and $n+1$
    codes the old element $n$. Set
    $$\begin{aligned}
    D^+&:=\lambdaab{o}{\lambdaab{n}{U(N(n),Do(\LambdaPred\,n))}},\\
    a(z)&:=p_1z,\qquad b(z):=p_2z,\\
    V(o,z)&:=Ro(\LambdaNumericPair\,(\LambdaPred\,a(z))\,(\LambdaPred\,b(z))),\\
    R^+&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(N(N(a(z))))\,U(N(b(z)),V(o,z))}}.
    \end{aligned}$$
    Expand the abbreviations with fresh binders. Equivalently, compose the numerical reindexing and Boolean-program
    constructors; on numeral inputs
    they perform these same bit computations.
    The empty presentation uses constant-zero programs for both membership and comparison.
-/
noncomputable def empty (ε : ℕ → ℕ) : WellOrderPresentation ε where
  domain _ := False
  relation _ _ := False
  domain_decidable := by simpa using (decidablePredicate_true ℕ ε).not
  relation_decidable := by simpa using (decidablePredicate_true (ℕ × ℕ) ε).not
  wellOrder := by
    let : IsEmpty {n : ℕ // False} := ⟨fun x => x.property⟩
    infer_instance

theorem empty_orderType (ε : ℕ → ℕ) : (empty ε).orderType = 0 := by
  let : IsEmpty (empty ε).Carrier := ⟨fun x => x.property⟩
  exact Ordinal.type_eq_zero_of_empty _

instance presentations_countable : Countable (WellOrderPresentation ε) := by
  let := countable_decidablePredicates ℕ ε
  let := countable_decidablePredicates (ℕ × ℕ) ε
  let f (W : WellOrderPresentation ε) :
      {D : ℕ → Prop // DecidablePredicate ε D} ×
      {R : ℕ × ℕ → Prop // DecidablePredicate ε R} :=
    (⟨W.domain,W.domain_decidable⟩,⟨fun z => W.relation z.1 z.2,W.relation_decidable⟩)
  apply Function.Injective.countable (f := f)
  intro W V h
  have hd : W.domain = V.domain := congrArg (fun p => p.1.val) h
  have hr : W.relation = V.relation := by
    have hpair := congrArg (fun p => p.2.val) h
    funext a b
    exact congrFun hpair (a,b)
  cases W
  cases V
  dsimp only at hd hr
  cases hd
  cases hr
  rfl

theorem orderType_countable (W : WellOrderPresentation ε) :
    W.orderType.card ≤ Cardinal.aleph0 := by
  rw [orderType,Ordinal.card_type]
  exact Cardinal.mk_le_aleph0

/-- The new domain tests membership and comparison with one fixed old element. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For an element with code $a$ in the original domain, the initial-segment membership program is
    $$D_{<a}:=\lambdaab{o}{\lambdaab{n}{\LambdaMul\,(Do\,n)\,
     (Ro(\LambdaNumericPair\,n\,\ChurchNumeral{a}))}}.$$
    Its comparison program remains $R$. For the successor, zero codes the new largest element and $n+1$
    codes the old element $n$. Set
    $$\begin{aligned}
    D^+&:=\lambdaab{o}{\lambdaab{n}{U(N(n),Do(\LambdaPred\,n))}},\\
    a(z)&:=p_1z,\qquad b(z):=p_2z,\\
    V(o,z)&:=Ro(\LambdaNumericPair\,(\LambdaPred\,a(z))\,(\LambdaPred\,b(z))),\\
    R^+&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(N(N(a(z))))\,U(N(b(z)),V(o,z))}}.
    \end{aligned}$$
    Expand the abbreviations with fresh binders. Equivalently, compose the numerical reindexing and Boolean-program
    constructors; on numeral inputs
    they perform these same bit computations.
    The empty presentation uses constant-zero programs for both membership and comparison.
-/
noncomputable def initial (W : WellOrderPresentation ε) (a : W.Carrier) :
    WellOrderPresentation ε where
  domain n := W.domain n ∧ W.relation n a.val
  relation := W.relation
  domain_decidable := W.domain_decidable.and
    (W.relation_decidable.precompNumerical (g := fun n : ℕ => (n,a.val))
      (numericalIdentity_computes.pair (numericalConstant_computes a.val)) (fun _ => rfl))
  relation_decidable := W.relation_decidable
  wellOrder := by
    let f : (fun x y : {n // W.domain n ∧ W.relation n a.val} => W.relation x.val y.val) ↪r W.order :=
      { toFun := fun x => ⟨x.val,x.property.1⟩
        inj' := fun _ _ h => Subtype.ext (congrArg (fun x : W.Carrier => x.val) h)
        map_rel_iff' := Iff.rfl }
    exact f.isWellOrder

noncomputable def initialIso (W : WellOrderPresentation ε) (a : W.Carrier) :
    (W.initial a).order ≃r Subrel W.order (W.order · a) where
  toFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  invFun x := ⟨x.val.val,x.val.property,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem initial_orderType (W : WellOrderPresentation ε) (a : W.Carrier) :
    (W.initial a).orderType = Ordinal.typein W.order a := by
  rw [orderType,(W.initialIso a).ordinalType_congr,Ordinal.type_subrel]

/-- Code the added largest element by zero and an old element n by n+1. -/
def successorDomain (W : WellOrderPresentation ε) (n : ℕ) : Prop :=
  n = 0 ∨ W.domain (n-1)

def successorRelation (W : WellOrderPresentation ε) (a b : ℕ) : Prop :=
  a ≠ 0 ∧ (b = 0 ∨ W.relation (a-1) (b-1))

noncomputable def successorEquiv (W : WellOrderPresentation ε) :
    {n // W.successorDomain n} ≃ W.Carrier ⊕ Unit where
  toFun
    | ⟨0,_⟩ => Sum.inr ()
    | ⟨n+1,h⟩ => Sum.inl ⟨n,by simpa [successorDomain] using h⟩
  invFun
    | Sum.inl x => ⟨x.val+1,by simpa [successorDomain] using x.property⟩
    | Sum.inr _ => ⟨0,Or.inl rfl⟩
  left_inv := by rintro ⟨_ | n,h⟩ <;> rfl
  right_inv := by rintro (x | ⟨⟩) <;> rfl

noncomputable def successorIso (W : WellOrderPresentation ε) :
    (fun a b : {n // W.successorDomain n} => W.successorRelation a.val b.val) ≃r
      Sum.Lex W.order (@emptyRelation Unit) where
  toEquiv := W.successorEquiv
  map_rel_iff' := by
    rintro ⟨_ | a,ha⟩ ⟨_ | b,hb⟩ <;> simp [successorEquiv,successorRelation,order]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For an element with code $a$ in the original domain, the initial-segment membership program is
    $$D_{<a}:=\lambdaab{o}{\lambdaab{n}{\LambdaMul\,(Do\,n)\,
     (Ro(\LambdaNumericPair\,n\,\ChurchNumeral{a}))}}.$$
    Its comparison program remains $R$. For the successor, zero codes the new largest element and $n+1$
    codes the old element $n$. Set
    $$\begin{aligned}
    D^+&:=\lambdaab{o}{\lambdaab{n}{U(N(n),Do(\LambdaPred\,n))}},\\
    a(z)&:=p_1z,\qquad b(z):=p_2z,\\
    V(o,z)&:=Ro(\LambdaNumericPair\,(\LambdaPred\,a(z))\,(\LambdaPred\,b(z))),\\
    R^+&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(N(N(a(z))))\,U(N(b(z)),V(o,z))}}.
    \end{aligned}$$
    Expand the abbreviations with fresh binders. Equivalently, compose the numerical reindexing and Boolean-program
    constructors; on numeral inputs
    they perform these same bit computations.
    The empty presentation uses constant-zero programs for both membership and comparison.
-/
noncomputable def successor (W : WellOrderPresentation ε) : WellOrderPresentation ε where
  domain := W.successorDomain
  relation := W.successorRelation
  domain_decidable := decidablePredicate_or_for_ordinals (decidable_zero ε)
    (W.domain_decidable.precompNumerical (g := fun n : ℕ => n-1) predecessor_computes (fun _ => rfl))
  relation_decidable := by
    have hf := (decidable_zero ε).not.precompNumerical (g := fun z : ℕ × ℕ => z.1)
      (projection_computes true) (by intro z; simp [Encodable.encode,Encodable.encodeSigma])
    have hs := (decidable_zero ε).precompNumerical (g := fun z : ℕ × ℕ => z.2)
      (projection_computes false) (by intro z; simp [Encodable.encode,Encodable.encodeSigma])
    have hr := W.relation_decidable.precompNumerical (g := fun z : ℕ × ℕ => (z.1-1,z.2-1))
      ((predecessor_computes.comp (projection_computes true)).pair
        (predecessor_computes.comp (projection_computes false))) (by intro z; simp [Encodable.encode,Encodable.encodeSigma])
    exact hf.and (decidablePredicate_or_for_ordinals hs hr)
  wellOrder := W.successorIso.toRelEmbedding.isWellOrder

theorem successor_orderType (W : WellOrderPresentation ε) :
    W.successor.orderType = W.orderType + 1 := by
  let := W.successorIso.toRelEmbedding.isWellOrder
  change Ordinal.type (fun a b : {n // W.successorDomain n} => W.successorRelation a.val b.val) = _
  rw [W.successorIso.ordinalType_congr,Ordinal.type_sum_lex,Ordinal.type_eq_one_of_unique (@emptyRelation Unit)]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Decision programs for initial segments and successors
  excerpt: |
    The displayed terms decide the initial-segment and successor presentations at the original parameter.
    They terminate on every numerical input. The corresponding order types are the position of $a$ and the
    successor of the original order type, respectively.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    In the initial-segment term, pairing supplies the original comparison input and multiplication computes
    conjunction. For the successor domain, $N(n)$ is one at zero, so $U$ accepts zero; at a positive input,
    predecessor recovers the old element and $U$ returns its membership bit. In the comparison term, the first
    factor is zero when the first input is zero. If that input is positive, the second factor is one when
    the second input is zero, and otherwise it is the comparison bit of the two predecessors. These are
    exactly the stated order clauses. All component calls terminate, even when a discarded old comparison
    is evaluated. The initial-segment inclusion is an order isomorphism onto the elements below $a$.
    For the successor, send a positive code to its predecessor and send zero to a new last point; this is
    an order isomorphism with the ordered sum of the old domain and a singleton.
    \end{proof}
-/
theorem initial_successor_presentations (W : WellOrderPresentation ε) (a : W.Carrier) :
    DecidablePredicate ε (W.initial a).domain ∧
    DecidablePredicate ε (fun z : ℕ × ℕ => (W.initial a).relation z.1 z.2) ∧
    DecidablePredicate ε W.successor.domain ∧
    DecidablePredicate ε (fun z : ℕ × ℕ => W.successor.relation z.1 z.2) ∧
    (W.initial a).orderType = Ordinal.typein W.order a ∧
    W.successor.orderType = W.orderType + 1 :=
  ⟨(W.initial a).domain_decidable,(W.initial a).relation_decidable,
    W.successor.domain_decidable,W.successor.relation_decidable,
    W.initial_orderType a,W.successor_orderType⟩

end WellOrderPresentation

/-- Relative recursiveness is represented by a decidable numerical well order. -/
def RecursiveOrdinal (ε : ℕ → ℕ) (o : Ordinal) : Prop :=
  ∃ W : WellOrderPresentation ε, W.orderType = o

theorem recursiveOrdinal_downward {ε : ℕ → ℕ} {o p : Ordinal}
    (ho : RecursiveOrdinal ε o) (hp : p < o) : RecursiveOrdinal ε p := by
  obtain ⟨W,rfl⟩ := ho
  obtain ⟨a,ha⟩ := Ordinal.typein_surj (r := W.order) hp
  exact ⟨W.initial a,(W.initial_orderType a).trans ha⟩

theorem recursiveOrdinal_successor {ε : ℕ → ℕ} {o : Ordinal}
    (ho : RecursiveOrdinal ε o) : RecursiveOrdinal ε (o+1) := by
  obtain ⟨W,rfl⟩ := ho
  exact ⟨W.successor,W.successor_orderType⟩

theorem recursiveOrdinal_zero (ε : ℕ → ℕ) : RecursiveOrdinal ε 0 :=
  ⟨WellOrderPresentation.empty ε,WellOrderPresentation.empty_orderType ε⟩

theorem recursiveOrdinal_nat (ε : ℕ → ℕ) (n : ℕ) : RecursiveOrdinal ε n := by
  induction n with
  | zero => exact recursiveOrdinal_zero ε
  | succ n ih => simpa only [Nat.cast_add,Nat.cast_one] using recursiveOrdinal_successor ih

noncomputable def recursiveOrdinalBound (ε : ℕ → ℕ) : Ordinal :=
  ⨆ W : WellOrderPresentation ε, W.orderType

theorem recursiveOrdinalBound_countable (ε : ℕ → ℕ) :
    (recursiveOrdinalBound ε).card ≤ Cardinal.aleph0 := by
  apply Ordinal.card_iSup_le Cardinal.mk_le_aleph0
  exact WellOrderPresentation.orderType_countable

theorem recursiveOrdinal_le_bound {ε : ℕ → ℕ} {o : Ordinal}
    (ho : RecursiveOrdinal ε o) : o ≤ recursiveOrdinalBound ε := by
  obtain ⟨W,rfl⟩ := ho
  exact Ordinal.le_iSup _ W

theorem recursiveOrdinal_of_lt_bound {ε : ℕ → ℕ} {o : Ordinal}
    (ho : o < recursiveOrdinalBound ε) : RecursiveOrdinal ε o := by
  obtain ⟨W,hW⟩ := Ordinal.lt_iSup_iff.mp ho
  exact recursiveOrdinal_downward ⟨W,rfl⟩ hW

theorem recursiveOrdinal_lt_bound {ε : ℕ → ℕ} {o : Ordinal}
    (ho : RecursiveOrdinal ε o) : o < recursiveOrdinalBound ε :=
  lt_of_lt_of_le (lt_add_one o) (recursiveOrdinal_le_bound (recursiveOrdinal_successor ho))

theorem recursiveOrdinalBound_not_recursive (ε : ℕ → ℕ) :
    ¬ RecursiveOrdinal ε (recursiveOrdinalBound ε) := by
  intro h
  exact (lt_irrefl _) (recursiveOrdinal_lt_bound h)

theorem recursiveOrdinal_iff_lt_bound (ε : ℕ → ℕ) (o : Ordinal) :
    RecursiveOrdinal ε o ↔ o < recursiveOrdinalBound ε :=
  ⟨recursiveOrdinal_lt_bound,recursiveOrdinal_of_lt_bound⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Boundary of relative recursive ordinals
  excerpt: |
    For each fixed $\varepsilon$, the ordinal $\relativeChurchKleeneOrd{\varepsilon}$ is countable and has no
    presentation recursive relative to $\varepsilon$. An ordinal has such a presentation if and only if it is
    strictly below $\relativeChurchKleeneOrd{\varepsilon}$. In particular, $\churchKleeneOrd$ is the least
    nonrecursive ordinal.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    There are countably many domain and comparison predicates at a fixed parameter: choose numerical indices
    for their two closed decision programs, and use uniqueness of outputs. Hence there are countably many
    presentations. Every domain is a subset of $\NN$, so every order type is countable. Their supremum is
    countable as well, by the countability of a countable union of countable sets. This argument does not
    decide which program pairs present well orders.

    Two concrete operations on presentations finish the proof. Given $a\in D$, keep the comparison relation
    and replace the domain by
    $$D_{<a}:=\{n\in D:n\mathrel R a\}.$$
    Its decider multiplies the membership bit and the comparison bit with the fixed constant $a$. Its order
    type is the position of $a$ in the original well order. Every smaller ordinal occurs at such a position,
    so the represented ordinals are downward closed.

    For a successor, put
    $$D^+:=\{0\}\cup\{n+1:n\in D\}.$$
    Make zero the largest element, with
    $$n+1\mathrel{R^+}0,\qquad
     n+1\mathrel{R^+}(m+1)\ \Longleftrightarrow\ n\mathrel R m,$$
    and no comparison $0\mathrel{R^+}b$. Zero testing, predecessor, and the old two deciders give total
    programs for this presentation; their explicit terms are in §{sec:lambda-recursive-order-programs}.
    The map sending $n$ to $n+1$, together with the new largest element, identifies its order type with the
    old order type plus one. The empty domain presents zero, so finite iteration also presents every finite ordinal.

    Every represented ordinal is therefore strictly below the supremum: its successor is still represented.
    The supremum cannot itself be represented, for then its successor would exceed the supremum. Finally,
    if an ordinal is strictly below the supremum, some presented order type exceeds it; the initial-segment
    construction gives a presentation of that ordinal. This proves all the assertions.
    \end{proof}
-/
theorem recursiveOrdinal_boundary (ε : ℕ → ℕ) :
    (recursiveOrdinalBound ε).card ≤ Cardinal.aleph0 ∧
    ¬ RecursiveOrdinal ε (recursiveOrdinalBound ε) ∧
    ∀ o, RecursiveOrdinal ε o ↔ o < recursiveOrdinalBound ε :=
  ⟨recursiveOrdinalBound_countable ε,recursiveOrdinalBound_not_recursive ε,
    recursiveOrdinal_iff_lt_bound ε⟩

end LambdaRelative
end PolishSpaceBook
