module

public import PolishSpaceBook.BorelExpressionNatCertificates

@[expose] public section

/-! # Constructors and extensional completeness of Borel expressions

A new root grafts the supplied expression below each child. Complement has only
child zero; countable union has every child. The well-foundedness proof follows
the grafted subtrees, and evaluation follows the same node equations.
-/
namespace PolishSpaceBook
open Set
namespace BorelExpression

def basic (n : ℕ) : BorelExpression
  | [] => n + 3
  | _ :: _ => 0

def absent : BorelExpression := fun _ => 0

def graft (label : ℕ) (c : ℕ → BorelExpression) : BorelExpression
  | [] => label
  | i :: s => c i s

def union (c : ℕ → BorelExpression) : BorelExpression := graft 1 c

def complement (c : BorelExpression) : BorelExpression :=
  graft 2 (fun i => if i = 0 then c else absent)

@[simp] theorem graft_nil (label : ℕ) (c : ℕ → BorelExpression) : graft label c [] = label := rfl
@[simp] theorem graft_cons (label : ℕ) (c : ℕ → BorelExpression) (i : ℕ) (s : List ℕ) :
    graft label c (i :: s) = c i s := rfl
@[simp] theorem union_nil (c : ℕ → BorelExpression) : union c [] = 1 := rfl
@[simp] theorem union_cons (c : ℕ → BorelExpression) (i : ℕ) (s : List ℕ) :
    union c (i :: s) = c i s := rfl
@[simp] theorem complement_nil (c : BorelExpression) : complement c [] = 2 := rfl
@[simp] theorem complement_cons (c : BorelExpression) (i : ℕ) (s : List ℕ) :
    complement c (i :: s) = if i = 0 then c s else 0 := by
  by_cases hi : i = 0 <;> simp [complement,graft,hi,absent]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For a finite word $s$, write $(i)\concat s$ for the word obtained by adjoining $i$ at the beginning.
    The constructors from §{sec:borel-codes-construction} act on label maps as follows:
    $$\begin{aligned}
    \BorelLeafCode{n}(\emptySeq)&:=n+3,&
    \BorelLeafCode{n}((i)\concat s)&:=0,\\
    \BorelComplementCode{c}(\emptySeq)&:=2,&
    \BorelComplementCode{c}((i)\concat s)&:=
     \begin{cases}c(s)&i=0,\\0&i>0,\end{cases}\\
    \BorelUnionCode{(c_i)}(\emptySeq)&:=1,&
    \BorelUnionCode{(c_i)}((i)\concat s)&:=c_i(s).
    \end{aligned}$$
    Thus a complement adds a root with one subtree, while a union attaches the $i$th expression below child $i$.
    The first operation consists of a single leaf.
-/
/-- The constructors implement the displayed root and subtree label equations. -/
theorem constructor_labels (n i : ℕ) (s : List ℕ) (c : BorelExpression)
    (family : ℕ → BorelExpression) :
    basic n [] = n + 3 ∧ basic n (i :: s) = 0 ∧
    complement c [] = 2 ∧ complement c (i :: s) = (if i = 0 then c s else 0) ∧
    union family [] = 1 ∧ union family (i :: s) = family i s := by
  simp [basic]

theorem wellFounded_absent : WellFounded absent.Child := by
  constructor
  intro s
  exact Acc.intro s (fun t ht => False.elim (ht.1 rfl))

theorem wellFounded_graft (label : ℕ) (c : ℕ → BorelExpression)
    (hc : ∀ i, WellFounded (c i).Child) : WellFounded (graft label c).Child := by
  have hcons (i : ℕ) (s : List ℕ) : Acc (graft label c).Child (i :: s) := by
    induction s using (hc i).induction with
    | h s ih =>
      constructor
      rintro t ⟨hs,k,rfl,ht⟩
      exact ih (s ++ [k]) ⟨hs,k,rfl,ht⟩
  constructor
  intro s
  cases s with
  | nil =>
    constructor
    rintro t ⟨_,k,rfl,_⟩
    exact hcons k []
  | cons i s => exact hcons i s

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    The single leaf satisfies all validity conditions. For the other two constructions, prefix closure and
    all local label conditions follow from those in the attached expressions. Every attached root is present,
    so the new union root has children and the new complement root has exactly one child.
    A descending child chain, after entering child $i$, stays in that subtree. Removing its initial $i$
    would give a descending chain in the attached expression. Thus the new child relation is well founded.
    More explicitly, well-founded induction inside each attached expression proves accessibility of every
    node below the new root; accessibility of the root follows because all its children are accessible.

    Restrict the evaluation to the subtree below child $i$ and remove the initial $i$ from its node addresses.
    The resulting assignment satisfies exactly the evaluation equations for the attached expression.
    Uniqueness of evaluation by well-founded induction therefore identifies the two assignments.
    The root equation now gives the stated union or complement. At a single leaf it gives $U_n$ directly.
-/
theorem valid_basic (n : ℕ) : (basic n).Valid := by
  refine ⟨by simp [basic],?_,?_,?_,?_,?_⟩
  · intro s k h
    cases s <;> simp [basic] at h
  · intro s hs k
    cases s <;> simp [basic]
  · intro s hs
    cases s <;> simp [basic] at hs
  · intro s hs
    cases s <;> simp [basic] at hs
  · constructor
    intro s
    constructor
    rintro t ⟨_,k,rfl,ht⟩
    cases s <;> simp [basic] at ht

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    The single leaf satisfies all validity conditions. For the other two constructions, prefix closure and
    all local label conditions follow from those in the attached expressions. Every attached root is present,
    so the new union root has children and the new complement root has exactly one child.
    A descending child chain, after entering child $i$, stays in that subtree. Removing its initial $i$
    would give a descending chain in the attached expression. Thus the new child relation is well founded.
    More explicitly, well-founded induction inside each attached expression proves accessibility of every
    node below the new root; accessibility of the root follows because all its children are accessible.

    Restrict the evaluation to the subtree below child $i$ and remove the initial $i$ from its node addresses.
    The resulting assignment satisfies exactly the evaluation equations for the attached expression.
    Uniqueness of evaluation by well-founded induction therefore identifies the two assignments.
    The root equation now gives the stated union or complement. At a single leaf it gives $U_n$ directly.
-/
theorem valid_union (c : ℕ → BorelExpression) (hc : ∀ i, (c i).Valid) : (union c).Valid := by
  refine ⟨by simp [union,graft],?_,?_,?_,?_,wellFounded_graft 1 c (fun i => (hc i).2.2.2.2.2)⟩
  · intro s k h
    cases s with
    | nil => simp [union,graft]
    | cons i s => exact (hc i).2.1 s k h
  · intro s hs k
    cases s with
    | nil => simp [union,graft] at hs
    | cons i s => exact (hc i).2.2.1 s hs k
  · intro s hs
    cases s with
    | nil => exact ⟨0,(hc 0).1⟩
    | cons i s => exact (hc i).2.2.2.1 s hs
  · intro s hs
    cases s with
    | nil => simp [union,graft] at hs
    | cons i s => exact (hc i).2.2.2.2.1 s hs

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    The single leaf satisfies all validity conditions. For the other two constructions, prefix closure and
    all local label conditions follow from those in the attached expressions. Every attached root is present,
    so the new union root has children and the new complement root has exactly one child.
    A descending child chain, after entering child $i$, stays in that subtree. Removing its initial $i$
    would give a descending chain in the attached expression. Thus the new child relation is well founded.
    More explicitly, well-founded induction inside each attached expression proves accessibility of every
    node below the new root; accessibility of the root follows because all its children are accessible.

    Restrict the evaluation to the subtree below child $i$ and remove the initial $i$ from its node addresses.
    The resulting assignment satisfies exactly the evaluation equations for the attached expression.
    Uniqueness of evaluation by well-founded induction therefore identifies the two assignments.
    The root equation now gives the stated union or complement. At a single leaf it gives $U_n$ directly.
-/
theorem valid_complement (c : BorelExpression) (hc : c.Valid) : (complement c).Valid := by
  have hw : ∀ i, WellFounded ((if i = 0 then c else absent) : BorelExpression).Child := by
    intro i
    split_ifs <;> [exact hc.2.2.2.2.2; exact wellFounded_absent]
  refine ⟨by simp [complement,graft],?_,?_,?_,?_,wellFounded_graft 2 _ hw⟩
  · intro s k h
    cases s with
    | nil => simp [complement,graft]
    | cons i s =>
      by_cases hi : i = 0
      · simpa [complement,graft,hi] using hc.2.1 s k (by simpa [complement,graft,hi] using h)
      · simp [complement,graft,hi,absent] at h
  · intro s hs k
    cases s with
    | nil => simp [complement,graft] at hs
    | cons i s =>
      by_cases hi : i = 0
      · simpa [complement,graft,hi] using hc.2.2.1 s (by simpa [complement,graft,hi] using hs) k
      · simp [complement,graft,hi,absent] at hs
  · intro s hs
    cases s with
    | nil => simp [complement,graft] at hs
    | cons i s =>
      by_cases hi : i = 0
      · simpa [complement,graft,hi] using hc.2.2.2.1 s (by simpa [complement,graft,hi] using hs)
      · simp [complement,graft,hi,absent] at hs
  · intro s hs
    cases s with
    | nil =>
      refine ⟨0,by simpa [complement,graft] using hc.1,?_⟩
      intro i hi
      by_contra h
      simp [complement,graft,h,absent] at hi
    | cons i s =>
      by_cases hi : i = 0
      · simpa [complement,graft,hi] using hc.2.2.2.2.1 s (by simpa [complement,graft,hi] using hs)
      · simp [complement,graft,hi,absent] at hs

theorem SetEvaluation.graft_section {X : Type*} {label : ℕ} {c : ℕ → BorelExpression}
    {U : ℕ → Set X} {A : List ℕ → Set X} (h : (graft label c).SetEvaluation U A) (i : ℕ) :
    (c i).SetEvaluation U (fun s => A (i :: s)) := by
  intro s
  simpa [graft] using h (i :: s)

theorem evaluate_graft_cons {X : Type*} (label : ℕ) (c : ℕ → BorelExpression)
    (hc : ∀ i, WellFounded (c i).Child) (U : ℕ → Set X) (i : ℕ) (s : List ℕ) :
    (graft label c).evaluate (wellFounded_graft label c hc) U (i :: s) =
      (c i).evaluate (hc i) U s := by
  have h := ((graft label c).evaluate_isEvaluation (wellFounded_graft label c hc) U).graft_section i
  exact congrFun (h.unique (hc i) ((c i).evaluate_isEvaluation (hc i) U)) s

/-- The set denoted at the root; proof irrelevance makes the validity proof immaterial. -/
noncomputable def denotes {X : Type*} (c : BorelExpression) (hc : c.Valid) (U : ℕ → Set X) : Set X :=
  c.evaluate hc.2.2.2.2.2 U []

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Borel-expression constructors
  excerpt: |
    These operations preserve validity. For valid $c$ and $c_i$,
    $$\BorelValue{\BorelLeafCode{n}}=U_n,\qquad
    \BorelValue{\BorelComplementCode{c}}=(\BorelValue{c})^{\complement},\qquad
    \BorelValue{\BorelUnionCode{(c_i)}}=\bigcup_i\BorelValue{c_i}.$$
-/
theorem denotes_basic {X : Type*} (U : ℕ → Set X) (n : ℕ) :
    (basic n).denotes (valid_basic n) U = U n := by
  rw [denotes,(basic n).evaluate_isEvaluation]
  simp [basic]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Borel-expression constructors
  excerpt: |
    These operations preserve validity. For valid $c$ and $c_i$,
    $$\BorelValue{\BorelLeafCode{n}}=U_n,\qquad
    \BorelValue{\BorelComplementCode{c}}=(\BorelValue{c})^{\complement},\qquad
    \BorelValue{\BorelUnionCode{(c_i)}}=\bigcup_i\BorelValue{c_i}.$$
-/
theorem denotes_union {X : Type*} (U : ℕ → Set X) (c : ℕ → BorelExpression)
    (hc : ∀ i, (c i).Valid) : (union c).denotes (valid_union c hc) U = ⋃ i, (c i).denotes (hc i) U := by
  let hw := wellFounded_graft 1 c (fun i => (hc i).2.2.2.2.2)
  change (graft 1 c).evaluate hw U [] = _
  rw [(graft 1 c).evaluate_isEvaluation hw U []]
  simp only [graft_nil,graft_cons,List.nil_append,one_ne_zero,ite_false,ite_true]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, by rwa [evaluate_graft_cons 1 c (fun i => (hc i).2.2.2.2.2)] at hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨i, (hc i).1, by rwa [evaluate_graft_cons 1 c (fun i => (hc i).2.2.2.2.2)]⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Borel-expression constructors
  excerpt: |
    These operations preserve validity. For valid $c$ and $c_i$,
    $$\BorelValue{\BorelLeafCode{n}}=U_n,\qquad
    \BorelValue{\BorelComplementCode{c}}=(\BorelValue{c})^{\complement},\qquad
    \BorelValue{\BorelUnionCode{(c_i)}}=\bigcup_i\BorelValue{c_i}.$$
-/
theorem denotes_complement {X : Type*} (U : ℕ → Set X) (c : BorelExpression) (hc : c.Valid) :
    (complement c).denotes (valid_complement c hc) U = (c.denotes hc U)ᶜ := by
  have hzero : (complement c).evaluate (valid_complement c hc).2.2.2.2.2 U [0] = c.denotes hc U :=
    evaluate_graft_cons 2 (fun i => if i = 0 then c else absent)
      (fun i => by split_ifs <;> [exact hc.2.2.2.2.2;exact wellFounded_absent]) U 0 []
  rw [denotes,(complement c).evaluate_isEvaluation]
  simp only [complement_nil,complement_cons,List.nil_append,show (2:ℕ) ≠ 0 by decide,
    show (2:ℕ) ≠ 1 by decide,ite_false,ite_true]
  congr 1
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k,hk,hx⟩
    have hk0 : k = 0 := by by_contra h; simp [h] at hk
    subst k
    rwa [hzero] at hx
  · intro hx
    exact ⟨0,by simpa using hc.1,by rwa [hzero]⟩

end BorelExpression
end PolishSpaceBook
