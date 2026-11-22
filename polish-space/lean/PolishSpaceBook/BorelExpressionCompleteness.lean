module

public import PolishSpaceBook.BorelExpressionConstructors

@[expose] public section

/-! # Every Borel set has an external valid expression

The denotations form a sigma algebra containing the chosen generators. This is
extensional completeness; choosing an external code is not a computation of a
recursive code from arbitrary set data.
-/
namespace PolishSpaceBook
open Set MeasureTheory TopologicalSpace NamedLambda
namespace BorelExpression

def HasCode {X : Type*} (U : ℕ → Set X) (A : Set X) : Prop :=
  ∃ c : BorelExpression, ∃ hc : c.Valid, c.denotes hc U = A

theorem hasCode_basic {X : Type*} (U : ℕ → Set X) (n : ℕ) : HasCode U (U n) :=
  ⟨basic n,valid_basic n,denotes_basic U n⟩

theorem HasCode.compl {X : Type*} {U : ℕ → Set X} {A : Set X} (h : HasCode U A) : HasCode U Aᶜ := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨complement c,valid_complement c hc,denotes_complement U c hc⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $\mathcal C$ consist of the sets having valid expressions. It contains each basic cylinder by the
    leaf construction. The empty word codes $U_0=\BaireSpace$, so the complement of that leaf codes the empty
    set. The complement construction closes $\mathcal C$ under complements. Given a sequence of sets in
    $\mathcal C$, choose a valid expression for each; the union construction codes their union. Thus
    $\mathcal C$ is a sigma-algebra containing the cylinder basis, and hence contains every Borel set.
    Conversely, well-founded induction on an expression shows that every value in its evaluation is Borel:
    leaves are cylinders, complement nodes take complements, and union nodes take countable unions.
    Apply this at the root.
-/
theorem HasCode.iUnion {X : Type*} {U : ℕ → Set X} {A : ℕ → Set X}
    (h : ∀ i, HasCode U (A i)) : HasCode U (⋃ i, A i) := by
  classical
  choose c hc he using h
  refine ⟨union c,valid_union c hc,?_⟩
  rw [denotes_union U c hc]
  exact iUnion_congr he

@[reducible] def codedMeasurableSpace {X : Type*} (U : ℕ → Set X) (hU : U 0 = univ) : MeasurableSpace X where
  MeasurableSet' := HasCode U
  measurableSet_empty := by simpa only [hU,compl_univ] using (hasCode_basic U 0).compl
  measurableSet_compl := fun _ h => h.compl
  measurableSet_iUnion := fun _ h => HasCode.iUnion h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Let $\mathcal C$ consist of the sets having valid expressions. It contains each basic cylinder by the
    leaf construction. The empty word codes $U_0=\BaireSpace$, so the complement of that leaf codes the empty
    set. The complement construction closes $\mathcal C$ under complements. Given a sequence of sets in
    $\mathcal C$, choose a valid expression for each; the union construction codes their union. Thus
    $\mathcal C$ is a sigma-algebra containing the cylinder basis, and hence contains every Borel set.
    Conversely, well-founded induction on an expression shows that every value in its evaluation is Borel:
    leaves are cylinders, complement nodes take complements, and union nodes take countable unions.
    Apply this at the root.
-/
theorem hasCode_of_generateFrom {X : Type*} (U : ℕ → Set X) (hU : U 0 = univ)
    {A : Set X} (hA : MeasurableSet[MeasurableSpace.generateFrom (Set.range U)] A) : HasCode U A := by
  have hle : MeasurableSpace.generateFrom (Set.range U) ≤ codedMeasurableSpace U hU := by
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨n,rfl⟩
    exact hasCode_basic U n
  exact hle A hA

theorem borel_eq_generateFrom_cylinderBasis :
    borel (ℕ → ℕ) = MeasurableSpace.generateFrom (Set.range cylinderBasis) := by
  have he : ({U : Set (ℕ → ℕ) | ∃ s : List ℕ, U = cyl s}) = Set.range cylinderBasis := by
    ext U
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨NatListCode.encode s,by simp [cylinderBasis]⟩
    · rintro ⟨n,rfl⟩
      exact ⟨NatListCode.decode n,rfl⟩
  rw [← he]
  exact isTopologicalBasis_cyl.borel_eq_generateFrom

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Completeness of external Borel expressions
  excerpt: |
    A subset of $\BaireSpace$ is Borel if and only if it is $\BorelValue{c}$ for some valid expression $c$.
-/
theorem measurableSet_iff_hasCode (A : Set (ℕ → ℕ)) : MeasurableSet A ↔ HasCode cylinderBasis A := by
  constructor
  · intro hA
    apply hasCode_of_generateFrom cylinderBasis (by simp [cylinderBasis,NatListCode.decode])
    rw [← borel_eq_generateFrom_cylinderBasis]
    have hm : (inferInstance : MeasurableSpace (ℕ → ℕ)) = borel (ℕ → ℕ) :=
      BorelSpace.measurable_eq
    rw [← hm]
    exact hA
  · rintro ⟨c,hc,rfl⟩
    exact c.measurableSet_evaluate hc.2.2.2.2.2 cylinderBasis (fun n => (isOpen_cyl _).measurableSet) []

end BorelExpression
end PolishSpaceBook
