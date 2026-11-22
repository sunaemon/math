module

public import PolishSpaceBook.TreeWellFounded
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

/-! # The Kleene--Brouwer order of a well-founded tree

Proper extensions precede their prefixes. At the first differing coordinate,
the smaller natural number comes first. Well-foundedness is proved by choosing
a least occupied child, with induction on strict extension in the original tree.
-/
namespace PolishSpaceBook
namespace KleeneBrouwer

/-- Lexicographic comparison with the end of a word larger than every digit. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    For finite words $s,t$, define the \termdefine{Kleene--Brouwer order} by placing a proper extension before
    its prefix and otherwise comparing the first differing entries. Equivalently, its clauses are
    $$\begin{aligned}
    &\neg(\kleeneBrouwerOrder{[]}{t}),\qquad \kleeneBrouwerOrder{a::s}{[]},\\
    &\kleeneBrouwerOrder{a::s}{b::t}
     \quad\Longleftrightarrow\quad a<b\ \lor\ (a=b\ \land\ \kleeneBrouwerOrder{s}{t}).
    \end{aligned}$$
    Thus the end of a word is treated as larger than every natural-number entry. This is a strict linear
    order on finite words. It need not be well founded on all finite words.
-/
def Before : List ℕ → List ℕ → Prop
  | [], _ => False
  | _ :: _, [] => True
  | a :: s, b :: t => a < b ∨ a = b ∧ Before s t

@[simp] theorem before_nil_left (s : List ℕ) : ¬ Before [] s := by cases s <;> simp [Before]
@[simp] theorem before_cons_nil (a : ℕ) (s : List ℕ) : Before (a :: s) [] := trivial
@[simp] theorem before_cons (a b : ℕ) (s t : List ℕ) :
    Before (a :: s) (b :: t) ↔ a < b ∨ a = b ∧ Before s t := Iff.rfl

@[simp] theorem before_self (s : List ℕ) : ¬ Before s s := by
  induction s with
  | nil => simp
  | cons a s ih => simp [ih]

theorem before_trans {s t u : List ℕ} (hst : Before s t) (htu : Before t u) : Before s u := by
  induction s generalizing t u with
  | nil => simp at hst
  | cons a s ih =>
    cases t with
    | nil => simp at htu
    | cons b t =>
      cases u with
      | nil => trivial
      | cons c u =>
        simp only [before_cons] at *
        rcases hst with h | ⟨rfl,h⟩ <;> rcases htu with h' | ⟨rfl,h'⟩
        · exact Or.inl (h.trans h')
        · exact Or.inl h
        · exact Or.inl h'
        · exact Or.inr ⟨rfl,ih h h'⟩

theorem before_trichotomy (s t : List ℕ) : Before s t ∨ s = t ∨ Before t s := by
  induction s generalizing t with
  | nil => cases t <;> simp
  | cons a s ih =>
    cases t with
    | nil => exact Or.inl trivial
    | cons b t =>
      rcases lt_trichotomy a b with h | rfl | h
      · exact Or.inl (Or.inl h)
      · rcases ih t with h | rfl | h
        · exact Or.inl (Or.inr ⟨rfl,h⟩)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨rfl,h⟩))
      · exact Or.inr (Or.inr (Or.inl h))

instance : IsStrictTotalOrder (List ℕ) Before where
  irrefl := before_self
  trans _ _ _ := before_trans
  trichotomous a b hab hba := (before_trichotomy a b).resolve_left hab |>.resolve_right hba

@[simp] theorem before_append (s t u : List ℕ) : Before (s ++ t) (s ++ u) ↔ Before t u := by
  induction s with
  | nil => rfl
  | cons a s ih => simpa using ih

theorem not_before_extension (s t : List ℕ) : ¬ Before s (s ++ t) := by
  have h := before_append s [] t
  simpa only [List.append_nil] using h.not.mpr (before_nil_left t)

theorem before_of_strict_prefix {s t : List ℕ} (h : s.IsPrefix t) (hne : s ≠ t) : Before t s := by
  obtain ⟨u,rfl⟩ := h
  cases u with
  | nil => simp at hne
  | cons a u =>
    simpa only [List.append_nil] using (before_append s (a :: u) []).mpr (before_cons_nil a u)

/-- Each nonempty subset of the cone above a node has a least member. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The comparison clauses give irreflexivity, transitivity, and trichotomy by induction on words. We prove
    well-foundedness by induction on strict extension in $T$. At a node $s$, the induction assertion is that
    every nonempty subset $A$ of its cone has a least element in the Kleene--Brouwer order. If $A$ contains
    no proper extension of $s$, its only element is $s$. Otherwise, choose the least $n$ such that the cone
    above $s\concat(n)$ meets $A$, where $s\concat(n)$ denotes appending $n$ to $s$. The child $s\concat(n)$ belongs to
    $T$ by closure under prefixes. The induction hypothesis gives a least element $m$ in that intersection.
    Every other member of $A$ is either $s$, lies above the same child, or lies above a child with larger
    index. In the first and third cases it follows after $m$; in the second it cannot precede $m$ by the
    choice of $m$. This proves the induction assertion. For a nonempty tree apply it at the empty word;
    the empty tree is immediate. The choices here prove well-foundedness and are not asserted to be
    computable from an arbitrary subset $A$.

    List encoding is a bijection with $\NN$, so the original membership program decides the domain of
    codes without any extra validity test. The comparison clauses give a total lambda program by recursion
    on the first word, as constructed in §{sec:lambda-kleene-brouwer}. This comparison makes no parameter
    queries. Consequently the coded order is a presentation at the original $\varepsilon$, and its order
    type $\alpha$ is below $\relativeChurchKleeneOrd{\varepsilon}$.

    Every strict extension precedes its prefix in this order. Induction on strict extension therefore
    bounds the rank of each node by its position in the well order: the successor of each child rank is
    at most the position of its parent, and taking their supremum preserves that inequality. Each such
    position is strictly below $\alpha$, proving the displayed bound. For a rooted tree apply it at the
    root. The constant-zero parameter gives the final assertion.
    \end{proof}
-/
theorem cone_has_min {T : Set (List ℕ)} (hT : IsSubtree T)
    (hw : WellFounded (strictTreeExtension T)) (s : T) :
    ∀ A : Set T, (∃ t ∈ A, s.val.IsPrefix t.val) →
      ∃ m ∈ A, s.val.IsPrefix m.val ∧
        ∀ t ∈ A, s.val.IsPrefix t.val → ¬ Before t.val m.val := by
  classical
  induction s using hw.induction with
  | h s ih =>
    intro A hA
    let P (n : ℕ) := ∃ t ∈ A, (s.val ++ [n]).IsPrefix t.val
    by_cases hp : ∃ n, P n
    · let n := Nat.find hp
      obtain ⟨t,ht,hst⟩ := Nat.find_spec hp
      have hnT : s.val ++ [n] ∈ T := hT t.property hst
      let c : T := ⟨s.val ++ [n],hnT⟩
      have hcs : strictTreeExtension T c s := ⟨List.prefix_append _ _,by simp [c]⟩
      obtain ⟨m,hm,hcm,hmin⟩ := ih c hcs A ⟨t,ht,hst⟩
      refine ⟨m,hm,(List.prefix_append s.val [n]).trans hcm,?_⟩
      intro u hu hsu hbefore
      obtain ⟨v,hv⟩ := hsu
      cases v with
      | nil =>
        have heq : u.val = s.val := by simpa using hv.symm
        obtain ⟨w,hw⟩ := (List.prefix_append s.val [n]).trans hcm
        exact not_before_extension s.val w (by simpa [heq,← hw] using hbefore)
      | cons k v =>
        have hku : (s.val ++ [k]).IsPrefix u.val := by
          rw [← hv]
          exact ⟨v,by simp⟩
        have hnk : n ≤ k := Nat.find_min' hp ⟨u,hu,hku⟩
        obtain ⟨w,hw⟩ := hcm
        have hk : k < n ∨ k = n ∧ Before v w := by
          simpa [← hv,← hw,c,List.append_assoc] using hbefore
        have heq : k = n := by rcases hk with hk | hk <;> omega
        exact hmin u hu (by simpa [heq] using hku) hbefore
    · obtain ⟨t,ht,hst⟩ := hA
      have only (u : T) (hu : u ∈ A) (hsu : s.val.IsPrefix u.val) : u = s := by
        obtain ⟨v,hv⟩ := hsu
        cases v with
        | nil => exact Subtype.ext (by simpa using hv.symm)
        | cons k v =>
          exfalso
          apply hp
          refine ⟨k,u,hu,?_⟩
          rw [← hv]
          exact ⟨v,by simp⟩
      have hts := only t ht hst
      subst t
      exact ⟨s,ht,List.prefix_refl _,fun u hu hsu => by rw [only u hu hsu]; simp⟩

theorem wellFounded {T : Set (List ℕ)} (hT : IsSubtree T)
    (hw : WellFounded (strictTreeExtension T)) :
    WellFounded (fun s t : T => Before s.val t.val) := by
  classical
  rw [WellFounded.wellFounded_iff_has_min]
  intro A hA
  obtain ⟨t,ht⟩ := hA
  have hroot : [] ∈ T := hT t.property List.nil_prefix
  obtain ⟨m,hm,_,hmin⟩ := cone_has_min hT hw ⟨[],hroot⟩ A ⟨t,ht,List.nil_prefix⟩
  exact ⟨m,hm,fun u hu => hmin u hu List.nil_prefix⟩

instance tree_strictTotal (T : Set (List ℕ)) :
    IsStrictTotalOrder T (fun s t => Before s.val t.val) :=
  { irrefl := fun s => before_self s.val
    trans := fun _ _ _ => before_trans
    trichotomous := fun a b hab hba => Subtype.ext
      ((before_trichotomy a.val b.val).resolve_left hab |>.resolve_right hba) }

/-- Strict extension is contained in Kleene--Brouwer comparison. -/
theorem extension_before {T : Set (List ℕ)} {s t : T} (h : strictTreeExtension T s t) :
    Before s.val t.val :=
  before_of_strict_prefix h.1 (fun he => by have := h.2; simp [he] at this)

end KleeneBrouwer
end PolishSpaceBook
