module

public import PolishSpaceBook.NonnegativeRealCutAdditionFormula

@[expose] public section

/-! # Decoding finitely additive measures given by graphs of nonnegative real codes -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels
universe u

/-- The finite measure axioms on a ring of sets. No countable additivity on external families is asserted. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We now read the finite measure laws from a graph of values. Let $D$ be a family of subsets of an ambient
    set $Y$, containing $\emptyset$ and closed under binary unions and differences. Let $R$ be a set of valid
    nonnegative real cut codes, and let $F:D\to R$ be a function graph. In an internal interpretation, the
    whole sets $D,R,F$ belong to the transitive model $M$. The arithmetic parameters used below also belong
    to $M$ by §{sec:internal-natural-arithmetic}.
-/
structure FiniteAdditiveCutGraph (D R F : ZFSet.{u}) : Prop where
  function : IsFunc D R F
  valid : ∀ C ∈ R, ValidNonnegativeRealCutCode C
  empty_mem : (∅ : ZFSet.{u}) ∈ D
  zero : pair ∅ ∅ ∈ F
  union_mem : ∀ A ∈ D, ∀ B ∈ D, A ∪ B ∈ D
  diff_mem : ∀ A ∈ D, ∀ B ∈ D, A \ B ∈ D
  add : ∀ A ∈ D, ∀ B ∈ D, Disjoint (A : Set ZFSet) (B : Set ZFSet) →
    ∀ C E V, pair A C ∈ F → pair B E ∈ F → pair (A ∪ B) V ∈ F → V = sumCutCode C E

namespace FiniteAdditiveCutGraph
variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

/-- Values outside the domain default to the zero code; laws are stated only for domain elements. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $A\in D$, write $\MeasureValueCode{F}{A}$ for the unique code with
    $\langle A,\MeasureValueCode{F}{A}\rangle\in F$, and put
    $$\nu(A):=\RealCutValue{\MeasureValueCode{F}{A}}.$$
-/
def code (A : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hA : A ∈ D then Classical.choose (h.function.2 A hA) else ∅

lemma pair_code {A : ZFSet.{u}} (hA : A ∈ D) : pair A (h.code A) ∈ F := by
  rw [code, dite_eq_left hA]
  exact (Classical.choose_spec (h.function.2 A hA)).1

lemma code_mem {A : ZFSet.{u}} (hA : A ∈ D) : h.code A ∈ R :=
  (ZFSet.pair_mem_prod.mp (h.function.1 (h.pair_code hA))).2

lemma code_valid {A : ZFSet.{u}} (hA : A ∈ D) : ValidNonnegativeRealCutCode (h.code A) :=
  h.valid _ (h.code_mem hA)

lemma code_eq {A C : ZFSet.{u}} (hA : A ∈ D) (hp : pair A C ∈ F) : h.code A = C :=
  ((h.function.2 A hA).unique (h.pair_code hA) hp)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $A\in D$, write $\MeasureValueCode{F}{A}$ for the unique code with
    $\langle A,\MeasureValueCode{F}{A}\rangle\in F$, and put
    $$\nu(A):=\RealCutValue{\MeasureValueCode{F}{A}}.$$
-/
def value (A : ZFSet.{u}) : ℝ := decodeNonnegativeRealCut (h.code A)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Validity of the value codes gives nonnegativity. The zero clause and uniqueness of the graph value give
    the empty code at $\emptyset$, which decodes to zero. For two disjoint sets, the graph clause and
    §{sec:internal-real-cut-addition} give addition of the decoded values. Induction on a finite list of
    pairwise disjoint sets proves the displayed finite-union formula; the empty list uses the zero clause.
    For $A\IncludedIn B$, split $B$ into the disjoint sets $A$ and $\SetDifference{B}{A}$ to obtain
    $$\nu(A)+\nu(\SetDifference{B}{A})=\nu(B).$$
    Nonnegativity gives monotonicity. Taking $B=Y$ and using $\nu(Y)=1$ gives the complement formula.
-/
lemma value_nonneg {A : ZFSet.{u}} (hA : A ∈ D) : 0 ≤ h.value A :=
  decodeNonnegativeRealCut_nonneg (h.code_valid hA)

lemma value_zero : h.value ∅ = 0 := by
  have he := h.code_eq h.empty_mem h.zero
  rw [value, he, ← nonnegativeRealCutCode_zero, decode_nonnegativeRealCutCode (le_refl 0)]

lemma value_of_code {A : ZFSet.{u}} (hA : A ∈ D) {r : ℝ} (hr : 0 ≤ r)
    (hp : pair A (nonnegativeRealCutCode r) ∈ F) : h.value A = r := by
  rw [value, h.code_eq hA hp, decode_nonnegativeRealCutCode hr]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Decoding finite measure axioms
-/
theorem value_union {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D)
    (hd : Disjoint (A : Set ZFSet) (B : Set ZFSet)) :
    h.value (A ∪ B) = h.value A + h.value B := by
  have he := h.add A hA B hB hd (h.code A) (h.code B) (h.code (A ∪ B))
    (h.pair_code hA) (h.pair_code hB) (h.pair_code (h.union_mem A hA B hB))
  exact (congrArg decodeNonnegativeRealCut he).trans (decode_sumCutCode (h.code_valid hA) (h.code_valid hB))

lemma value_sdiff_add {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D) (hab : A ⊆ B) :
    h.value A + h.value (B \ A) = h.value B := by
  have hd : Disjoint (A : Set ZFSet) ((B \ A : ZFSet) : Set ZFSet) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (ZFSet.mem_sdiff.mp hy).2 hx
  have he : A ∪ (B \ A) = B := by
    ext x
    simp only [ZFSet.mem_union, ZFSet.mem_sdiff]
    exact ⟨fun h => h.elim (fun hx => hab hx) And.left,
      fun hx => by by_cases ha : x ∈ A; exact Or.inl ha; exact Or.inr ⟨hx, ha⟩⟩
  have hadd := h.value_union hA (h.diff_mem B hB A hA) hd
  rw [he] at hadd
  exact hadd.symm

lemma value_mono {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D) (hab : A ⊆ B) :
    h.value A ≤ h.value B := by
  have hadd := h.value_sdiff_add hA hB hab
  have hn := h.value_nonneg (h.diff_mem B hB A hA)
  linarith

lemma value_complement {Y A : ZFSet.{u}} (hY : Y ∈ D) (hA : A ∈ D) (haY : A ⊆ Y)
    (hunit : h.value Y = 1) : h.value (Y \ A) = 1 - h.value A := by
  have hadd := h.value_sdiff_add hA hY haY
  rw [hunit] at hadd
  linarith

/-- The finite union represented by a list of sets. -/
def listUnion : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | A :: l => A ∪ listUnion l

lemma mem_listUnion (l : List ZFSet.{u}) (x : ZFSet.{u}) : x ∈ listUnion l ↔ ∃ A ∈ l, x ∈ A := by
  induction l with
  | nil => simp [listUnion]
  | cons A l ih => simp [listUnion, ih]

include h in
lemma listUnion_mem (l : List ZFSet.{u}) (hl : ∀ A ∈ l, A ∈ D) : listUnion l ∈ D := by
  induction l with
  | nil => exact h.empty_mem
  | cons A l ih => exact h.union_mem A (hl A (by simp)) _ (ih (fun B hB => hl B (by simp [hB])))

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Decoding finite measure axioms
-/
theorem value_listUnion (l : List ZFSet.{u}) (hl : ∀ A ∈ l, A ∈ D)
    (hd : l.Pairwise (fun (A B : ZFSet.{u}) => Disjoint (A : Set ZFSet) (B : Set ZFSet))) :
    h.value (listUnion l) = (l.map h.value).sum := by
  induction l with
  | nil => simpa only [listUnion, List.map_nil, List.sum_nil] using h.value_zero
  | cons A l ih =>
    have hd' := List.pairwise_cons.mp hd
    have hl' : ∀ B ∈ l, B ∈ D := fun B hB => hl B (by simp [hB])
    have hdis : Disjoint (A : Set ZFSet) ((listUnion l : ZFSet) : Set ZFSet) := by
      rw [Set.disjoint_left]
      intro x hx hy
      obtain ⟨B, hB, hxB⟩ := (mem_listUnion l x).mp hy
      exact Set.disjoint_left.mp (hd'.1 B hB) hx hxB
    rw [listUnion, h.value_union (hl A (by simp)) (h.listUnion_mem l hl') hdis,
      ih hl' hd'.2, List.map_cons, List.sum_cons]

lemma value_listUnion_const (l : List ZFSet.{u}) (hl : ∀ A ∈ l, A ∈ D)
    (hd : l.Pairwise (fun (A B : ZFSet.{u}) => Disjoint (A : Set ZFSet) (B : Set ZFSet)))
    {r : ℝ} (hr : 0 ≤ r) (hv : ∀ A ∈ l, pair A (nonnegativeRealCutCode r) ∈ F) :
    h.value (listUnion l) = (l.length : ℝ) * r := by
  rw [h.value_listUnion l hl hd]
  have hm : l.map h.value = l.map (fun _ => r) :=
    List.map_congr_left (fun A hA => h.value_of_code (hl A hA) hr (hv A hA))
  rw [hm]
  simp

end FiniteAdditiveCutGraph
end PolishSpaceBook.CantorTreeMeasure
