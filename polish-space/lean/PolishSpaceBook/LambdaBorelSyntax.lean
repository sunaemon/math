module

public import PolishSpaceBook.LambdaUniformFamilies
public import PolishSpaceBook.BorelExpressionValidity
public import PolishSpaceBook.LambdaBorelEvaluation
public import PolishSpaceBook.LambdaArithmeticTrees

@[expose] public section

/-! # Numerical certificates for Borel-expression syntax

A total joint label program is supplied. The structural tests do not assert
well-foundedness and do not decide whether an arbitrary program index is total.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace BorelExpression

/-- One structural row: word, two tested children, and a chosen child. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For input $z=\NatPair{e}{\NatPair{i}{j}}$, projections recover these components and
    $i=\NatPair{w}{\NatPair{k}{\ell}}$. In the following bodies abbreviate
    $$\begin{aligned}
    \LambdaTermName{rootLabel}&:= \LambdaTermName{labelAt}(o,e, \ChurchNumeral{0}), \qquad
    \LambdaTermName{nodeLabel}:= \LambdaTermName{labelAt}(o,e,w),\\
    \LambdaTermName{childLabel}&:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w,k)), \quad
    \LambdaTermName{otherLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w, \ell)), \quad
    \LambdaTermName{witnessLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w,j)).
    \end{aligned}$$
    The five decision bits are
    $$\begin{aligned}
    \LambdaTermName{syntaxBit}_0&:=\LambdaTermName{zero}(\LambdaTermName{zero}\LambdaTermName{rootLabel}),\\
    \LambdaTermName{syntaxBit}_1&:= \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
    \LambdaTermName{childLabel}), \LambdaTermName{zero}( \LambdaTermName{zero} \LambdaTermName{nodeLabel})),\\
    \LambdaTermName{syntaxBit}_2&:= \LambdaTermName{implies}( \LambdaTermName{le}( \ChurchNumeral{3},
    \LambdaTermName{nodeLabel}), \LambdaTermName{zero} \LambdaTermName{childLabel}),\\
    \LambdaTermName{syntaxBit}_3&:= \LambdaTermName{implies}( \LambdaTermName{or}( \LambdaTermName{equal}(
    \LambdaTermName{nodeLabel}, \ChurchNumeral{1}), \LambdaTermName{equal}( \LambdaTermName{nodeLabel},
    \ChurchNumeral{2})), \LambdaTermName{zero}( \LambdaTermName{zero} \LambdaTermName{witnessLabel})),\\
    \LambdaTermName{syntaxBit}_4&:= \LambdaTermName{implies}( \LambdaTermName{equal}( \LambdaTermName{nodeLabel},
    \ChurchNumeral{2}), \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
    \LambdaTermName{childLabel}), \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
    \LambdaTermName{otherLabel}), \LambdaTermName{equal}(k, \ell)))).
    \end{aligned}$$
    Expand all abbreviations and numerical projections inside
    $$\LambdaTermName{syntaxRow}:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,\LambdaTermName{syntaxBit}_0\,
     ( \LambdaMul\, \LambdaTermName{syntaxBit}_1\,( \LambdaMul\, \LambdaTermName{syntaxBit}_2\,( \LambdaMul\,
    \LambdaTermName{syntaxBit}_3\, \LambdaTermName{syntaxBit}_4)))}}.$$
-/
def syntaxRow (c : BorelExpression) (i j : ℕ) : Prop :=
  let s := NatListCode.decode i.unpair.1
  let k := i.unpair.2.unpair.1
  let l := i.unpair.2.unpair.2
  c [] ≠ 0 ∧
  (c (s ++ [k]) ≠ 0 → c s ≠ 0) ∧
  (3 ≤ c s → c (s ++ [k]) = 0) ∧
  (c s = 1 ∨ c s = 2 → c (s ++ [j]) ≠ 0) ∧
  (c s = 2 → c (s ++ [k]) ≠ 0 → c (s ++ [l]) ≠ 0 → k = l)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $i=\NatPair{\LambdaListCode{s}}{\NatPair{k}{\ell}}$. For this row let $j$ be a proposed child and
    let $R(e,i,j)$ be the conjunction of
    $$\begin{aligned}
    c_e(\emptySeq)&\ne0,\\
    c_e(s\concat(k))\ne0&\ \Longrightarrow\ c_e(s)\ne0,\\
    3\le c_e(s)&\ \Longrightarrow\ c_e(s\concat(k))=0,\\
    c_e(s)=1\ \lor\ c_e(s)=2&\ \Longrightarrow\ c_e(s\concat(j))\ne0,\\
    c_e(s)=2\ \land\ c_e(s\concat(k))\ne0\ \land\ c_e(s\concat(\ell))\ne0
     &\ \Longrightarrow\ k=\ell.
    \end{aligned}$$
    These are finite, jointly decidable tests. The syntax conditions are equivalent to
    $\forall i\,\exists j\ R(e,i,j)$. In the forward direction, choose any present child at a union or
    complement node, and zero at other nodes. In the reverse direction, the row with $k=\ell=0$ supplies
    a present child at each union or complement node; the last clause, over all pairs of children,
    gives uniqueness at a complement. The other clauses give the root, prefix, and leaf conditions.
    The numerical-quantifier lemma therefore gives presentations of syntax and its failure.

    For failure of well-foundedness, let a witness $q$ store
    $$q(n)=\NatPair{\LambdaListCode{s_n}}{k_n}.$$
    Require $c_e(s_n)\ne0$, $c_e(s_{n+1})\ne0$, and $s_{n+1}=s_n\concat(k_n)$ for every $n$.
    Row $n$ needs only the first $n+2$ entries of the point and witness: the first point entry gives $e$,
    and two consecutive witness entries give the words and the chosen child. The label program is total,
    so these rows are decidable even on arbitrary finite words, with missing entries read as zero.
    The bounded-prefix construction yields a pair tree. A branch specifies an infinite child chain.
    Conversely, failure of well-foundedness supplies such a chain; record its words and the child number
    at each step to obtain a branch. This choice is used only to prove existence of a witness.

    An expression is invalid exactly when syntax fails or its child relation is not well-founded.
    Take the binary union of the two tree projections. The constructions of the row programs appear
    in §{sec:lambda-recursive-borel-separation}.
    \end{proof}
-/
theorem syntax_iff_rows (c : BorelExpression) :
    c.Syntax ↔ ∀ i, ∃ j, syntaxRow c i j := by
  classical
  constructor
  · rintro ⟨hroot,hparent,hleaf,hunion,hcompl⟩ i
    let s := NatListCode.decode i.unpair.1
    have hchoose : ∃ j, c s = 1 ∨ c s = 2 → c (s ++ [j]) ≠ 0 := by
      by_cases h1 : c s = 1
      · obtain ⟨j,hj⟩ := hunion s h1
        exact ⟨j,fun _ => hj⟩
      · by_cases h2 : c s = 2
        · obtain ⟨j,hj,_⟩ := hcompl s h2
          exact ⟨j,fun _ => hj⟩
        · exact ⟨0,by simp [h1,h2]⟩
    obtain ⟨j,hj⟩ := hchoose
    refine ⟨j,hroot,hparent s _,(fun h => hleaf s h _),hj,?_⟩
    intro h2 hk hl
    obtain ⟨a,_,ha⟩ := hcompl s h2
    exact (ha _ hk).trans (ha _ hl).symm
  · intro h
    have hs (s : List ℕ) (k l : ℕ) := h (Nat.pair (NatListCode.encode s) (Nat.pair k l))
    simp only [syntaxRow,Nat.unpair_pair,NatListCode.decode_encode] at hs
    refine ⟨(hs [] 0 0).choose_spec.1,?_,?_,?_,?_⟩
    · intro s k hk
      exact (hs s k 0).choose_spec.2.1 hk
    · intro s ha k
      exact (hs s k 0).choose_spec.2.2.1 ha
    · intro s ha
      obtain ⟨j,hj⟩ := hs s 0 0
      exact ⟨j,hj.2.2.2.1 (Or.inl ha)⟩
    · intro s ha
      obtain ⟨j,hj⟩ := hs s 0 0
      have hj' := hj.2.2.2.1 (Or.inr ha)
      refine ⟨j,hj',?_⟩
      intro k hk
      exact (hs s k j).choose_spec.2.2.2.2 ha hk hj'

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

/-- Labels are computed on the numerical pair of family index and word code. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Pairing, projections, list concatenation, and singleton formation all terminate with the displayed
    codes. The five label calls terminate by the hypothesis on $\LambdaTermName{familyLabels}$, retaining the same
    parameter.
    Equality, comparison, and zero tests return bits, and the five factors express exactly the five
    syntax clauses. Their product is one exactly when the whole row holds. The numerical-quantifier
    construction of §{sec:lambda-graph-tests} therefore applies to this closed row program.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $\LambdaTermName{familyLabels}$ be the supplied joint label program. For numeral arguments use the term
    abbreviations
    $$\begin{aligned}
    \LambdaTermName{childCode}(w,k)&:=\LambdaListAppend\,w\,(\LambdaListCons\,k\,\ChurchNumeral{0}),\\
    \LambdaTermName{labelAt}(o,e,w)&:=\LambdaTermName{familyLabels}o(\LambdaNumericPair\,e\,w),\\
    \LambdaTermName{equal}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaEqual\, \LambdaTermName{left}\,
    \LambdaTermName{right}, \qquad \LambdaTermName{zero}( \LambdaTermName{left}):= \LambdaTermName{equal}(
    \LambdaTermName{left}, \ChurchNumeral{0}),\\
    \LambdaTermName{le}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{ \LambdaTermName{left}}{
    \LambdaTermName{right}}{ \ChurchNumeral{1}}{ \ChurchNumeral{0}},\\
    \LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{
    \LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}},\\
    \LambdaTermName{or}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaTermName{zero}( \LambdaMul\,(
    \LambdaTermName{zero} \LambdaTermName{left})\,( \LambdaTermName{zero} \LambdaTermName{right})).
    \end{aligned}$$
    Thus $\LambdaTermName{zero}$ tests zero; on decision bits, $\LambdaTermName{implies}$ is implication and
    $\LambdaTermName{or}$ is disjunction.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For input $z=\NatPair{e}{\NatPair{i}{j}}$, projections recover these components and
    $i=\NatPair{w}{\NatPair{k}{\ell}}$. In the following bodies abbreviate
    $$\begin{aligned}
    \LambdaTermName{rootLabel}&:= \LambdaTermName{labelAt}(o,e, \ChurchNumeral{0}), \qquad
    \LambdaTermName{nodeLabel}:= \LambdaTermName{labelAt}(o,e,w),\\
    \LambdaTermName{childLabel}&:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w,k)), \quad
    \LambdaTermName{otherLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w, \ell)), \quad
    \LambdaTermName{witnessLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w,j)).
    \end{aligned}$$
    The five decision bits are
    $$\begin{aligned}
    \LambdaTermName{syntaxBit}_0&:=\LambdaTermName{zero}(\LambdaTermName{zero}\LambdaTermName{rootLabel}),\\
    \LambdaTermName{syntaxBit}_1&:= \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
    \LambdaTermName{childLabel}), \LambdaTermName{zero}( \LambdaTermName{zero} \LambdaTermName{nodeLabel})),\\
    \LambdaTermName{syntaxBit}_2&:= \LambdaTermName{implies}( \LambdaTermName{le}( \ChurchNumeral{3},
    \LambdaTermName{nodeLabel}), \LambdaTermName{zero} \LambdaTermName{childLabel}),\\
    \LambdaTermName{syntaxBit}_3&:= \LambdaTermName{implies}( \LambdaTermName{or}( \LambdaTermName{equal}(
    \LambdaTermName{nodeLabel}, \ChurchNumeral{1}), \LambdaTermName{equal}( \LambdaTermName{nodeLabel},
    \ChurchNumeral{2})), \LambdaTermName{zero}( \LambdaTermName{zero} \LambdaTermName{witnessLabel})),\\
    \LambdaTermName{syntaxBit}_4&:= \LambdaTermName{implies}( \LambdaTermName{equal}( \LambdaTermName{nodeLabel},
    \ChurchNumeral{2}), \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
    \LambdaTermName{childLabel}), \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
    \LambdaTermName{otherLabel}), \LambdaTermName{equal}(k, \ell)))).
    \end{aligned}$$
    Expand all abbreviations and numerical projections inside
    $$\LambdaTermName{syntaxRow}:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,\LambdaTermName{syntaxBit}_0\,
     ( \LambdaMul\, \LambdaTermName{syntaxBit}_1\,( \LambdaMul\, \LambdaTermName{syntaxBit}_2\,( \LambdaMul\,
    \LambdaTermName{syntaxBit}_3\, \LambdaTermName{syntaxBit}_4)))}}.$$
-/
theorem decidable_syntaxRow {ε : ℕ → ℕ} {C : AlphaTerm} (c : ℕ → BorelExpression)
    (hc : LambdaRelative.Computes ε C
      (fun z : ℕ => c z.unpair.1 (NatListCode.decode z.unpair.2))) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × ℕ) =>
      syntaxRow (c z.1) z.2.1 z.2.2) := by
  have he := projection_computes true
  have hi := (projection_computes true).comp (projection_computes false)
  have hj := (projection_computes false).comp (projection_computes false)
  have hs := (projection_computes true).comp hi
  have hk := (projection_computes true).comp ((projection_computes false).comp hi)
  have hl := (projection_computes false).comp ((projection_computes false).comp hi)
  have hlabel := fun {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) =>
    hc.reindex (he.pair hf)
  have hroot := hlabel (numericalConstant_computes 0)
  have ha := hlabel hs
  have hd := hlabel (rowChild_computes.comp (hs.pair hk))
  have hb := hlabel (rowChild_computes.comp (hs.pair hl))
  have hw := hlabel (rowChild_computes.comp (hs.pair hj))
  have hconst := fun n => LambdaRelative.ofNumerical (numericalConstant_computes n) ε
  have ha0 := (relative_eq ha (hconst 0)).not
  have ha1 := relative_eq ha (hconst 1)
  have ha2 := relative_eq ha (hconst 2)
  have hd0 := relative_eq hd (hconst 0)
  have hb0 := (relative_eq hb (hconst 0)).not
  have hw0 := (relative_eq hw (hconst 0)).not
  have hkl := relative_eq (LambdaRelative.ofNumerical hk ε) (LambdaRelative.ofNumerical hl ε)
  have h := ((relative_eq hroot (hconst 0)).not).and
    ((hd0.not.imp ha0).and ((relative_le (hconst 3) ha).imp hd0 |>.and
      (((ha1.or ha2).imp hw0).and (ha2.imp (hd0.not.imp (hb0.imp hkl))))))
  have ht := h.precompNumerical (g := fun z : ℕ × (ℕ × ℕ) => Nat.pair z.1 (Nat.pair z.2.1 z.2.2))
    numericalIdentity_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  simpa [syntaxRow,rowChild,rowWord,Nat.unpair_pair,NatListCode.decode_encode,
    NatListCode.decode] using ht

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $i=\NatPair{\LambdaListCode{s}}{\NatPair{k}{\ell}}$. For this row let $j$ be a proposed child and
    let $R(e,i,j)$ be the conjunction of
    $$\begin{aligned}
    c_e(\emptySeq)&\ne0,\\
    c_e(s\concat(k))\ne0&\ \Longrightarrow\ c_e(s)\ne0,\\
    3\le c_e(s)&\ \Longrightarrow\ c_e(s\concat(k))=0,\\
    c_e(s)=1\ \lor\ c_e(s)=2&\ \Longrightarrow\ c_e(s\concat(j))\ne0,\\
    c_e(s)=2\ \land\ c_e(s\concat(k))\ne0\ \land\ c_e(s\concat(\ell))\ne0
     &\ \Longrightarrow\ k=\ell.
    \end{aligned}$$
    These are finite, jointly decidable tests. The syntax conditions are equivalent to
    $\forall i\,\exists j\ R(e,i,j)$. In the forward direction, choose any present child at a union or
    complement node, and zero at other nodes. In the reverse direction, the row with $k=\ell=0$ supplies
    a present child at each union or complement node; the last clause, over all pairs of children,
    gives uniqueness at a complement. The other clauses give the root, prefix, and leaf conditions.
    The numerical-quantifier lemma therefore gives presentations of syntax and its failure.

    For failure of well-foundedness, let a witness $q$ store
    $$q(n)=\NatPair{\LambdaListCode{s_n}}{k_n}.$$
    Require $c_e(s_n)\ne0$, $c_e(s_{n+1})\ne0$, and $s_{n+1}=s_n\concat(k_n)$ for every $n$.
    Row $n$ needs only the first $n+2$ entries of the point and witness: the first point entry gives $e$,
    and two consecutive witness entries give the words and the chosen child. The label program is total,
    so these rows are decidable even on arbitrary finite words, with missing entries read as zero.
    The bounded-prefix construction yields a pair tree. A branch specifies an infinite child chain.
    Conversely, failure of well-foundedness supplies such a chain; record its words and the child number
    at each step to obtain a branch. This choice is used only to prove existence of a witness.

    An expression is invalid exactly when syntax fails or its child relation is not well-founded.
    Take the binary union of the two tree projections. The constructions of the row programs appear
    in §{sec:lambda-recursive-borel-separation}.
    \end{proof}
-/
theorem complemented_syntax {ε : ℕ → ℕ} {C : AlphaTerm} (c : ℕ → BorelExpression)
    (hc : LambdaRelative.Computes ε C
      (fun z : ℕ => c z.unpair.1 (NatListCode.decode z.unpair.2))) :
    LambdaTree.Complemented ε {x | (c (x 0)).Syntax} := by
  simpa only [syntax_iff_rows] using LambdaTree.complemented_forall_exists
    (R := fun e i j => syntaxRow (c e) i j) (decidable_syntaxRow c hc)

/-- A chain entry carries its word code and the child chosen for the next step. -/
def chainPair (c : BorelExpression) (a b : ℕ) : Prop :=
  c (NatListCode.decode a.unpair.1) ≠ 0 ∧
  c (NatListCode.decode b.unpair.1) ≠ 0 ∧
  b.unpair.1 = NatListCode.encode (NatListCode.decode a.unpair.1 ++ [a.unpair.2])

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $i=\NatPair{\LambdaListCode{s}}{\NatPair{k}{\ell}}$. For this row let $j$ be a proposed child and
    let $R(e,i,j)$ be the conjunction of
    $$\begin{aligned}
    c_e(\emptySeq)&\ne0,\\
    c_e(s\concat(k))\ne0&\ \Longrightarrow\ c_e(s)\ne0,\\
    3\le c_e(s)&\ \Longrightarrow\ c_e(s\concat(k))=0,\\
    c_e(s)=1\ \lor\ c_e(s)=2&\ \Longrightarrow\ c_e(s\concat(j))\ne0,\\
    c_e(s)=2\ \land\ c_e(s\concat(k))\ne0\ \land\ c_e(s\concat(\ell))\ne0
     &\ \Longrightarrow\ k=\ell.
    \end{aligned}$$
    These are finite, jointly decidable tests. The syntax conditions are equivalent to
    $\forall i\,\exists j\ R(e,i,j)$. In the forward direction, choose any present child at a union or
    complement node, and zero at other nodes. In the reverse direction, the row with $k=\ell=0$ supplies
    a present child at each union or complement node; the last clause, over all pairs of children,
    gives uniqueness at a complement. The other clauses give the root, prefix, and leaf conditions.
    The numerical-quantifier lemma therefore gives presentations of syntax and its failure.

    For failure of well-foundedness, let a witness $q$ store
    $$q(n)=\NatPair{\LambdaListCode{s_n}}{k_n}.$$
    Require $c_e(s_n)\ne0$, $c_e(s_{n+1})\ne0$, and $s_{n+1}=s_n\concat(k_n)$ for every $n$.
    Row $n$ needs only the first $n+2$ entries of the point and witness: the first point entry gives $e$,
    and two consecutive witness entries give the words and the chosen child. The label program is total,
    so these rows are decidable even on arbitrary finite words, with missing entries read as zero.
    The bounded-prefix construction yields a pair tree. A branch specifies an infinite child chain.
    Conversely, failure of well-foundedness supplies such a chain; record its words and the child number
    at each step to obtain a branch. This choice is used only to prove existence of a witness.

    An expression is invalid exactly when syntax fails or its child relation is not well-founded.
    Take the binary union of the two tree projections. The constructions of the row programs appear
    in §{sec:lambda-recursive-borel-separation}.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The labels are zero for an absent node, one for a union, two for a complement, and numbers at least
    three for basic-cylinder leaves. The structural conditions require a present root, prefix closure of
    present nodes, no children at a leaf, a present child at a union, and exactly one present child at a
    complement. Well-foundedness means that there is no infinite chain of present children. In this section,
    the label program is total jointly in the family index and the word code at the fixed parameter.
-/
theorem not_wellFounded_iff_chain (c : BorelExpression) :
    ¬ WellFounded c.Child ↔ ∃ q : ℕ → ℕ, ∀ n, chainPair c (q n) (q (n+1)) := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain,not_isEmpty_iff]
  constructor
  · rintro ⟨⟨f,hf⟩⟩
    have hh : ∀ n, ∃ k, f (n+1) = f n ++ [k] := fun n =>
      ⟨(hf n).2.choose,(hf n).2.choose_spec.1⟩
    choose k hk using hh
    refine ⟨fun n => Nat.pair (NatListCode.encode (f n)) (k n),fun n => ?_⟩
    simp only [chainPair,Nat.unpair_pair,NatListCode.decode_encode]
    exact ⟨(hf n).1,(hf n).2.choose_spec.2,congrArg NatListCode.encode (hk n)⟩
  · rintro ⟨q,hq⟩
    refine ⟨⟨fun n => NatListCode.decode (q n).unpair.1,fun n => ?_⟩⟩
    refine ⟨(hq n).1,(q n).unpair.2,?_,(hq n).2.1⟩
    change NatListCode.decode (q (n+1)).unpair.1 = _
    rw [(hq n).2.2,NatListCode.decode_encode]

local instance syntaxListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance syntaxPairEncoding : Encodable (List ℕ × List ℕ) := LambdaTree.wordPairEncodable

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a descending-chain row, the input is $z=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Use list access to obtain $e=s(0)$, $h_0=t(n)$, and $h_1=t(n+1)$, with zero for a missing entry.
    Put $w=\LambdaNumericProjection{1}h_0$, $k=\LambdaNumericProjection{2}h_0$, and
    $u=\LambdaNumericProjection{1}h_1$ inside the body
    $$\LambdaMul\,\bigl(\LambdaTermName{zero}(\LambdaTermName{zero}(\LambdaTermName{labelAt}(o,e,w)))\bigr)\,
     \bigl( \LambdaMul\,( \LambdaTermName{zero}( \LambdaTermName{zero}( \LambdaTermName{labelAt}(o,e,u))))\,(
    \LambdaTermName{equal}(u, \LambdaTermName{childCode}(w,k))) \bigr).$$
    Abstract $o,z$ after expanding the accessors. Its prefix bound is computed by
    $\lambdaab{n}{\LambdaSucc(\LambdaSucc n)}$.
-/
def finiteChainClause (c : ℕ → BorelExpression) (i : ℕ) (z : LambdaTree.PrefixPair) : Prop :=
  chainPair (c (z.1.getD 0 0)) (z.2.getD i 0) (z.2.getD (i+1) 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The first two factors require the current and next words to be present. The third compares the next
    word code with the code of the specified child. Since list coding is bijective, equality of these codes
    is precisely the required child relation. At prefix length $n+2$ all three list accesses are in range.
    The label calls terminate independently of the lengths of the words they encode. Thus the bounded-prefix
    construction gives exactly the chains in the validity proposition. No rank or test for well-foundedness
    is needed to compute these finite rows.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a descending-chain row, the input is $z=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Use list access to obtain $e=s(0)$, $h_0=t(n)$, and $h_1=t(n+1)$, with zero for a missing entry.
    Put $w=\LambdaNumericProjection{1}h_0$, $k=\LambdaNumericProjection{2}h_0$, and
    $u=\LambdaNumericProjection{1}h_1$ inside the body
    $$\LambdaMul\,\bigl(\LambdaTermName{zero}(\LambdaTermName{zero}(\LambdaTermName{labelAt}(o,e,w)))\bigr)\,
     \bigl( \LambdaMul\,( \LambdaTermName{zero}( \LambdaTermName{zero}( \LambdaTermName{labelAt}(o,e,u))))\,(
    \LambdaTermName{equal}(u, \LambdaTermName{childCode}(w,k))) \bigr).$$
    Abstract $o,z$ after expanding the accessors. Its prefix bound is computed by
    $\lambdaab{n}{\LambdaSucc(\LambdaSucc n)}$.
-/
theorem decidable_finiteChainClause {ε : ℕ → ℕ} {C : AlphaTerm} (c : ℕ → BorelExpression)
    (hc : LambdaRelative.Computes ε C
      (fun z : ℕ => c z.unpair.1 (NatListCode.decode z.unpair.2))) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × LambdaTree.PrefixPair =>
      finiteChainClause c z.1 z.2) := by
  have hi := projection_computes true
  have hs := (projection_computes true).comp (projection_computes false)
  have ht := (projection_computes false).comp (projection_computes false)
  have he := listGet_computes.comp (hs.pair (numericalConstant_computes 0))
  have ha := listGet_computes.comp (ht.pair hi)
  have hb := listGet_computes.comp (ht.pair (successor_computes.comp hi))
  have has := (projection_computes true).comp ha
  have hbs := (projection_computes true).comp hb
  have hlabela := hc.reindex (he.pair has)
  have hlabelb := hc.reindex (he.pair hbs)
  have hzero := LambdaRelative.ofNumerical (numericalConstant_computes 0) ε
  have hchild := rowChild_computes.comp ha
  have heq := relative_eq (LambdaRelative.ofNumerical hbs ε) (LambdaRelative.ofNumerical hchild ε)
  have h := ((relative_eq hlabela hzero).not).and (((relative_eq hlabelb hzero).not).and heq)
  have htyped := h.precompNumerical (g := fun z : ℕ × LambdaTree.PrefixPair =>
    Nat.pair z.1 (Nat.pair (NatListCode.encode z.2.1) (NatListCode.encode z.2.2)))
    numericalIdentity_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  simpa [finiteChainClause,chainPair,rowChild,rowWord,Nat.unpair_pair] using htyped

private theorem prefix_getD (x : ℕ → ℕ) {i n : ℕ} (hi : i < n) :
    (seqPrefix x n).getD i 0 = x i := by
  simp [seqPrefix,hi,List.getD_eq_getElem?_getD]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $i=\NatPair{\LambdaListCode{s}}{\NatPair{k}{\ell}}$. For this row let $j$ be a proposed child and
    let $R(e,i,j)$ be the conjunction of
    $$\begin{aligned}
    c_e(\emptySeq)&\ne0,\\
    c_e(s\concat(k))\ne0&\ \Longrightarrow\ c_e(s)\ne0,\\
    3\le c_e(s)&\ \Longrightarrow\ c_e(s\concat(k))=0,\\
    c_e(s)=1\ \lor\ c_e(s)=2&\ \Longrightarrow\ c_e(s\concat(j))\ne0,\\
    c_e(s)=2\ \land\ c_e(s\concat(k))\ne0\ \land\ c_e(s\concat(\ell))\ne0
     &\ \Longrightarrow\ k=\ell.
    \end{aligned}$$
    These are finite, jointly decidable tests. The syntax conditions are equivalent to
    $\forall i\,\exists j\ R(e,i,j)$. In the forward direction, choose any present child at a union or
    complement node, and zero at other nodes. In the reverse direction, the row with $k=\ell=0$ supplies
    a present child at each union or complement node; the last clause, over all pairs of children,
    gives uniqueness at a complement. The other clauses give the root, prefix, and leaf conditions.
    The numerical-quantifier lemma therefore gives presentations of syntax and its failure.

    For failure of well-foundedness, let a witness $q$ store
    $$q(n)=\NatPair{\LambdaListCode{s_n}}{k_n}.$$
    Require $c_e(s_n)\ne0$, $c_e(s_{n+1})\ne0$, and $s_{n+1}=s_n\concat(k_n)$ for every $n$.
    Row $n$ needs only the first $n+2$ entries of the point and witness: the first point entry gives $e$,
    and two consecutive witness entries give the words and the chosen child. The label program is total,
    so these rows are decidable even on arbitrary finite words, with missing entries read as zero.
    The bounded-prefix construction yields a pair tree. A branch specifies an infinite child chain.
    Conversely, failure of well-foundedness supplies such a chain; record its words and the child number
    at each step to obtain a branch. This choice is used only to prove existence of a witness.

    An expression is invalid exactly when syntax fails or its child relation is not well-founded.
    Take the binary union of the two tree projections. The constructions of the row programs appear
    in §{sec:lambda-recursive-borel-separation}.
    \end{proof}
-/
theorem projected_not_wellFounded {ε : ℕ → ℕ} {C : AlphaTerm} (c : ℕ → BorelExpression)
    (hc : LambdaRelative.Computes ε C
      (fun z : ℕ => c z.unpair.1 (NatListCode.decode z.unpair.2))) :
    LambdaTree.Projected ε {x | ¬ WellFounded (c (x 0)).Child} := by
  have h := LambdaTree.projected_forall_finitePrefixTests
    (p := finiteChainClause c) (decidable_finiteChainClause c hc)
    (numericalIdentity_computes.add (numericalConstant_computes 2))
  have heq : {x | ∃ q, ∀ i, finiteChainClause c i (seqPrefix x (i+2),seqPrefix q (i+2))} =
      {x | ¬ WellFounded (c (x 0)).Child} := by
    ext x
    have h0 (i : ℕ) : 0 < i+2 := by omega
    have h1 (i : ℕ) : i < i+2 := by omega
    have h2 (i : ℕ) : i+1 < i+2 := by omega
    simp only [mem_ofPred_eq,finiteChainClause,prefix_getD _ (h0 _),
      prefix_getD _ (h1 _),prefix_getD _ (h2 _)]
    exact (not_wellFounded_iff_chain (c (x 0))).symm
  exact heq ▸ h

/-- Invalidity is a relative tree projection for a uniformly total label family. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Validity in a uniformly computable Borel family
-/
theorem projected_not_valid {ε : ℕ → ℕ} {C : AlphaTerm} (c : ℕ → BorelExpression)
    (hc : LambdaRelative.Computes ε C
      (fun z : ℕ => c z.unpair.1 (NatListCode.decode z.unpair.2))) :
    LambdaTree.Projected ε {x | ¬ (c (x 0)).Valid} := by
  have hsyntax := LambdaTree.UniformProjected.const (complemented_syntax c hc).2
  have hchain := LambdaTree.UniformProjected.const (projected_not_wellFounded c hc)
  obtain ⟨T,_,hT⟩ := hsyntax.union hchain
  have h := (show LambdaTree.Projected ε
      (({x | (c (x 0)).Syntax} : Set (ℕ → ℕ))ᶜ ∪
        {x | ¬ WellFounded (c (x 0)).Child}) from ⟨T 0,hT 0⟩)
  convert h using 1
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff,valid_iff_syntax_wellFounded]
  tauto

end BorelExpression
end PolishSpaceBook
