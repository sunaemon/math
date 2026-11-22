module

public import PolishSpaceBook.SetTheoryPredicateComposition
public import PolishSpaceBook.SetTheoryFiniteCardinality

@[expose] public section

/-! # Entire class maps and set-coded quotients inside a transitive model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\begin{gathered}
    \EquivalenceClass{E}{a}:=\{b\in D:\langle a,b\rangle\in E\},\\
    q:=\{\langle a,\EquivalenceClass{E}{a}\rangle:a\in D\},\qquad
    \SetQuotient{D}{E}:=\GraphRange{q}.
    \end{gathered}$$
-/
def relationClass (D R a : ZFSet.{u}) : ZFSet.{u} := D.sep (fun b => pair a b ∈ R)

lemma mem_relationClass (D R a b : ZFSet.{u}) : b ∈ relationClass D R a ↔ b ∈ D ∧ pair a b ∈ R :=
  ZFSet.mem_sep

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\begin{gathered}
    \EquivalenceClass{E}{a}:=\{b\in D:\langle a,b\rangle\in E\},\\
    q:=\{\langle a,\EquivalenceClass{E}{a}\rangle:a\in D\},\qquad
    \SetQuotient{D}{E}:=\GraphRange{q}.
    \end{gathered}$$
-/
def relationClassMap (D R : ZFSet.{u}) : ZFSet.{u} := functionGraph (fun a : D => relationClass D R a.val)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\begin{gathered}
    \EquivalenceClass{E}{a}:=\{b\in D:\langle a,b\rangle\in E\},\\
    q:=\{\langle a,\EquivalenceClass{E}{a}\rangle:a\in D\},\qquad
    \SetQuotient{D}{E}:=\GraphRange{q}.
    \end{gathered}$$
-/
def relationQuotient (D R : ZFSet.{u}) : ZFSet.{u} := graphRange (relationClassMap D R)

lemma pair_mem_relationClassMap (D R : ZFSet.{u}) (a : D) (C : ZFSet.{u}) :
    pair a.val C ∈ relationClassMap D R ↔ relationClass D R a.val = C := pair_mem_functionGraph _ a C

lemma mem_relationQuotient (D R C : ZFSet.{u}) :
    C ∈ relationQuotient D R ↔ ∃ a ∈ D, relationClass D R a = C := by
  rw [relationQuotient, mem_graphRange]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := ZFSet.mem_range.mp ha
    obtain ⟨rfl, he⟩ := ZFSet.pair_inj.mp hb
    exact ⟨b.val, b.property, he⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (pair_mem_relationClassMap D R ⟨a, ha⟩ _).mpr rfl⟩

/-- Parameters carrier, relation, input, whole output class. -/
def relationClassPredicate : BoundedSetPredicate 4 :=
  setComprehension 0 3 (.pairMember 1 2 4)

lemma eval_relationClassPredicate (D R a C : ZFSet.{u}) :
    relationClassPredicate.eval ![D, R, a, C] ↔ C = relationClass D R a := by
  apply eval_setComprehension_iff_eq (0 : Fin 4) 3 _ ![D, R, a, C]
  · exact fun _ hx => (ZFSet.mem_sep.mp hx).1
  · intro b hb
    change b ∈ D at hb
    change (pair a b ∈ R) ↔ b ∈ relationClass D R a
    simp only [mem_relationClass, hb, true_and]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hsep in
lemma relationClass_mem (D R a : M) : relationClass D.val R.val a.val ∈ M :=
  (BoundedSetPredicate.pairMember (0 : Fin 3) 1 2).separation_mem hM (hsep _) ![R, a] D.property

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal quotient maps
-/
include hM hpair hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Bounded Separation gives each class. A candidate class is specified as a subset of the carrier whose
    members are exactly those related to the given input. The shared bounded-predicate interpretation
    and definable-graph construction therefore collect the whole graph by Replacement. Taking its range
    gives the quotient set. If two classes coincide, reflexivity puts the second representative in both
    classes, so the representatives are related. Conversely, symmetry and transitivity show that related
    representatives have the same class.
-/
theorem relationClassMap_mem (D R : M) : relationClassMap D.val R.val ∈ M := by
  let f (a : D.val) : M := ⟨relationClass D.val R.val a.val,
    relationClass_mem hM hsep D R ⟨a.val, hM.mem_trans a.property D.property⟩⟩
  apply replacement_graph_mem hM hpair relationClassPredicate.compile (hrep _) ![D, R] D.property f
  intro a C
  rw [relationClassPredicate.realize_compile hM]
  have he : Subtype.val ∘ Fin.snoc (Fin.snoc ![D, R] ⟨a.val, hM.mem_trans a.property D.property⟩) C = ![D.val, R.val, a.val, C.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_relationClassPredicate]
  change C.val = (f a).val ↔ C = f a
  exact Subtype.ext_iff.symm

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal quotient maps
-/
include hM hpair hunion hsep hrep in
theorem relationQuotient_mem (D R : M) : relationQuotient D.val R.val ∈ M :=
  graphRange_mem hM hunion (hsep _) (relationClassMap_mem hM hpair hsep hrep D R)

/-- The set-coded classes agree exactly with the canonical quotient by the given setoid. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal quotient maps
-/
theorem relationClass_eq_iff (D R : ZFSet.{u}) (s : Setoid D)
    (hs : ∀ a b : D, pair a.val b.val ∈ R ↔ s.r a b) (a b : D) :
    relationClass D R a.val = relationClass D R b.val ↔ s.r a b := by
  constructor
  · intro he
    have hb : b.val ∈ relationClass D R b.val := (mem_relationClass _ _ _ _).mpr
      ⟨b.property, (hs b b).mpr (s.refl b)⟩
    rw [← he] at hb
    exact (hs a b).mp ((mem_relationClass _ _ _ _).mp hb).2
  · intro hab
    ext c
    simp only [mem_relationClass]
    constructor
    · rintro ⟨hc, hac⟩
      exact ⟨hc, (hs b ⟨c, hc⟩).mpr (s.trans (s.symm hab) ((hs a ⟨c, hc⟩).mp hac))⟩
    · rintro ⟨hc, hbc⟩
      exact ⟨hc, (hs a ⟨c, hc⟩).mpr (s.trans hab ((hs b ⟨c, hc⟩).mp hbc))⟩

lemma relationClass_eq_quotient_iff (D R : ZFSet.{u}) (s : Setoid D)
    (hs : ∀ a b : D, pair a.val b.val ∈ R ↔ s.r a b) (a b : D) :
    relationClass D R a.val = relationClass D R b.val ↔ Quotient.mk s a = Quotient.mk s b := by
  rw [Quotient.eq, relationClass_eq_iff D R s hs]

end PolishSpaceBook.SetTheoryModels
