module

public import PolishSpaceBook.BorelExpressionConstructors

@[expose] public section

/-! # Valid Borel expressions with derived Boolean constructors -/
namespace PolishSpaceBook
open Set
namespace BorelExpression

abbrev Code := {c : BorelExpression // c.Valid}
namespace Code

def leaf (n : ℕ) : Code := ⟨basic n, valid_basic n⟩
def compl (c : Code) : Code := ⟨complement c.val, valid_complement c.val c.property⟩
def iUnion (c : ℕ → Code) : Code :=
  ⟨union (fun i => (c i).val), valid_union _ (fun i => (c i).property)⟩
def empty : Code := (leaf 0).compl
def iInter (c : ℕ → Code) : Code := (iUnion (fun i => (c i).compl)).compl
def sup (c d : Code) : Code := iUnion (fun i => if i = 0 then c else d)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Write $\BorelValue{c}$ for the set obtained by evaluating a valid expression $c$ at its root.
-/
noncomputable def value {X : Type*} (c : Code) (U : ℕ → Set X) : Set X :=
  c.val.denotes c.property U

theorem value_leaf {X : Type*} (U : ℕ → Set X) (n : ℕ) : (leaf n).value U = U n :=
  denotes_basic U n

theorem value_compl {X : Type*} (U : ℕ → Set X) (c : Code) :
    c.compl.value U = (c.value U)ᶜ := denotes_complement U c.val c.property

theorem value_iUnion {X : Type*} (U : ℕ → Set X) (c : ℕ → Code) :
    (iUnion c).value U = ⋃ i, (c i).value U :=
  denotes_union U (fun i => (c i).val) (fun i => (c i).property)

theorem value_empty {X : Type*} (U : ℕ → Set X) (hU : U 0 = univ) : empty.value U = ∅ := by
  rw [empty,value_compl,value_leaf,hU,compl_univ]

theorem value_iInter {X : Type*} (U : ℕ → Set X) (c : ℕ → Code) :
    (iInter c).value U = ⋂ i, (c i).value U := by
  simp [iInter,value_compl,value_iUnion]

theorem value_sup {X : Type*} (U : ℕ → Set X) (c d : Code) :
    (sup c d).value U = c.value U ∪ d.value U := by
  rw [sup,value_iUnion]
  ext x
  simp only [mem_iUnion,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    by_cases h : i = 0
    · exact Or.inl (by simpa [h] using hi)
    · exact Or.inr (by simpa [h] using hi)
  · rintro (h|h)
    · exact ⟨0,by simpa using h⟩
    · exact ⟨1,by simpa using h⟩

def inf (c d : Code) : Code := (sup c.compl d.compl).compl
def diff (c d : Code) : Code := inf c d.compl
def symmDiff (c d : Code) : Code := sup (diff c d) (diff d c)

theorem value_inf {X : Type*} (U : ℕ → Set X) (c d : Code) :
    (inf c d).value U = c.value U ∩ d.value U := by
  simp [inf, value_compl, value_sup]

theorem value_diff {X : Type*} (U : ℕ → Set X) (c d : Code) :
    (diff c d).value U = c.value U \ d.value U := by
  rw [diff, value_inf, value_compl]
  rfl

theorem value_symmDiff {X : Type*} (U : ℕ → Set X) (c d : Code) :
    (symmDiff c d).value U = (c.value U \ d.value U) ∪ (d.value U \ c.value U) := by
  rw [symmDiff, value_sup, value_diff, value_diff]

end Code
end BorelExpression
end PolishSpaceBook
