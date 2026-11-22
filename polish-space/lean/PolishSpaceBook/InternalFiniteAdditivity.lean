module

public import PolishSpaceBook.FiniteAdditiveCutGraphs

@[expose] public section

/-! # Bounded interpretation of the ordinary finite-additivity axiom -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- The union is characterized by its two inclusions and its elements. -/
def setUnionPredicate : BoundedSetPredicate 3 :=
  .conj (.subset 0 2) (.conj (.subset 1 2) (.all 2 (.disj (.member 3 0) (.member 3 1))))

lemma eval_setUnionPredicate (A B U : ZFSet.{u}) :
    setUnionPredicate.eval ![A, B, U] ↔ U = A ∪ B := by
  change (A ⊆ U ∧ B ⊆ U ∧ ∀ x ∈ U, x ∈ A ∨ x ∈ B) ↔ _
  constructor
  · rintro ⟨ha, hb, hu⟩
    ext x
    rw [ZFSet.mem_union]
    exact ⟨hu x, fun hx => hx.elim (fun h => ha h) (fun h => hb h)⟩
  · rintro rfl
    exact ⟨fun _ h => ZFSet.mem_union.mpr (Or.inl h),
      fun _ h => ZFSet.mem_union.mpr (Or.inr h), fun _ h => ZFSet.mem_union.mp h⟩

def setDisjointPredicate : BoundedSetPredicate 2 := .all 0 (.neg (.member 2 1))

lemma eval_setDisjointPredicate (A B : ZFSet.{u}) :
    setDisjointPredicate.eval ![A, B] ↔ Disjoint (A : Set ZFSet) (B : Set ZFSet) := by
  exact Set.disjoint_left.symm

/-- Parameters omega, multiplication, addition, zero, natural pairs, range, graph, A,B,U. -/
def finiteAdditivityInstancePredicate : BoundedSetPredicate 10 :=
  (BoundedSetPredicate.conj (setDisjointPredicate.rename ![(7 : Fin 10), 8])
    (setUnionPredicate.rename ![7, 8, 9])).imply
    (.all 5 (.all 5 (.all 5
      ((BoundedSetPredicate.conj (.pairMember (6 : Fin 13) 7 10)
        (.conj (.pairMember 6 8 11) (.pairMember 6 9 12))).imply
          (sumCutValuePredicate.rename ![0, 1, 2, 3, 4, 10, 11, 12])))))

lemma eval_finiteAdditivityInstancePredicate (R F A B U : ZFSet.{u}) :
    finiteAdditivityInstancePredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
      prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, R, F, A, B, U] ↔
      (Disjoint (A : Set ZFSet) (B : Set ZFSet) ∧ U = A ∪ B →
        ∀ C ∈ R, ∀ E ∈ R, ∀ V ∈ R,
          pair A C ∈ F ∧ pair B E ∈ F ∧ pair U V ∈ F → V = sumCutCode C E) := by
  let ps : Fin 10 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
    prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, R, F, A, B, U]
  have hd : ps ∘ ![(7 : Fin 10), 8] = ![A, B] := by funext i; fin_cases i <;> rfl
  have hu : ps ∘ ![(7 : Fin 10), 8, 9] = ![A, B, U] := by funext i; fin_cases i <;> rfl
  have hs (C E V : ZFSet.{u}) : Fin.snoc (Fin.snoc (Fin.snoc ps C) E) V ∘
      ![(0 : Fin 13), 1, 2, 3, 4, 10, 11, 12] = ![Ordinal.omega0.toZFSet,
        naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
        prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, C, E, V] := by
    funext i; fin_cases i <;> rfl
  change finiteAdditivityInstancePredicate.eval ps ↔ _
  simp only [finiteAdditivityInstancePredicate, eval_imply, eval, eval_rename, hd, hu, hs,
    eval_setDisjointPredicate, eval_setUnionPredicate, eval_sumCutValuePredicate]
  rfl

/-- Parameters omega, multiplication, addition, zero, natural pairs, domain, range, graph. -/
def finiteAdditivityPredicate : BoundedSetPredicate 8 :=
  .all 5 (.all 5 (.all 5
    (finiteAdditivityInstancePredicate.rename ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10])))

/-- The external reading retains the original domain and graph. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The zero clause is $\langle\emptyset,\emptyset\rangle\in F$.
    The finite-additivity clause says that for $A,B,U\in D$ and $C,E,V\in R$,
    $$\begin{gathered}
    A\cap B=\emptyset,\qquad U=A\cup B,\\
    \langle A,C\rangle\in F,\quad\langle B,E\rangle\in F,\quad\langle U,V\rangle\in F\\
    \Longrightarrow\quad V=\RealCutSum{C}{E}.
    \end{gathered}$$
    Denote this statement by $\FiniteAdditivityLaw{D}{R}{F}$, with the fixed arithmetic parameters understood.
    These are finite measure laws on the given family; countable additivity is not part of this clause.
-/
def FiniteAdditivityOnGraph (D R F : ZFSet.{u}) : Prop :=
  ∀ A ∈ D, ∀ B ∈ D, ∀ U ∈ D,
    Disjoint (A : Set ZFSet) (B : Set ZFSet) ∧ U = A ∪ B →
      ∀ C ∈ R, ∀ E ∈ R, ∀ V ∈ R,
        pair A C ∈ F ∧ pair B E ∈ F ∧ pair U V ∈ F → V = sumCutCode C E

def finiteAdditivityParameters (D R F : ZFSet.{u}) : Fin 8 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b),
    naturalBinaryGraph (fun a b => a + b), ∅,
    prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, D, R, F]

lemma eval_finiteAdditivityPredicate (D R F : ZFSet.{u}) :
    finiteAdditivityPredicate.eval (finiteAdditivityParameters D R F) ↔ FiniteAdditivityOnGraph D R F := by
  have he (A B U : ZFSet.{u}) :
      Fin.snoc (Fin.snoc (Fin.snoc (finiteAdditivityParameters D R F) A) B) U ∘
        ![(0 : Fin 11), 1, 2, 3, 4, 6, 7, 8, 9, 10] = ![Ordinal.omega0.toZFSet,
          naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
          prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, R, F, A, B, U] := by
    funext i; fin_cases i <;> rfl
  simp only [finiteAdditivityPredicate, eval, eval_rename, he, eval_finiteAdditivityInstancePredicate]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Absolute finite-additivity axiom
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Disjointness is the bounded test $\forall x\in A\;(x\notin B)$.
    The union equation says $A,B\IncludedIn U$ and $\forall x\in U\;(x\in A\lor x\in B)$.
    For the equation between value codes, require $V\IncludedIn\omega\times\omega$ and, for every pair in
    that ambient set, equivalence of membership in $V$ with the bounded sum condition from
    §{sec:internal-real-cut-addition}. The shared extensionality argument for a boundedly specified subset
    identifies this whole output set with $\RealCutSum{C}{E}$.
    All remaining quantifiers are bounded by $D$ or $R$, and graph lookup is bounded.
    The shared interpretation theorem therefore gives the equivalence. Function typing ensures that every
    actual value of $F$ belongs to $R$, so these range bounds omit no value.
-/
theorem realize_finiteAdditivityPredicate {M : ZFSet.{u}} (hM : M.IsTransitive)
    (ps : Fin 8 → M) (D R F : ZFSet.{u}) (hp : Subtype.val ∘ ps = finiteAdditivityParameters D R F) :
    finiteAdditivityPredicate.compile.Realize Empty.elim ps ↔ FiniteAdditivityOnGraph D R F := by
  rw [finiteAdditivityPredicate.realize_compile hM, hp, eval_finiteAdditivityPredicate]

/-- Convert the reflected axiom to the usual graph law; graph typing supplies all range bounds. -/
lemma finiteAdditivityOnGraph_add {D R F : ZFSet.{u}} (hf : IsFunc D R F)
    (hu : ∀ A ∈ D, ∀ B ∈ D, A ∪ B ∈ D) (ha : FiniteAdditivityOnGraph D R F)
    {A B C E V : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D)
    (hd : Disjoint (A : Set ZFSet) (B : Set ZFSet))
    (hAC : pair A C ∈ F) (hBE : pair B E ∈ F) (hUV : pair (A ∪ B) V ∈ F) : V = sumCutCode C E :=
  ha A hA B hB (A ∪ B) (hu A hA B hB) ⟨hd, rfl⟩
    C (ZFSet.pair_mem_prod.mp (hf.1 hAC)).2
    E (ZFSet.pair_mem_prod.mp (hf.1 hBE)).2
    V (ZFSet.pair_mem_prod.mp (hf.1 hUV)).2 ⟨hAC, hBE, hUV⟩

/-- The remaining hypotheses are the domain, value-typing and zero clauses of finite measure. -/
theorem finiteAdditiveCutGraph_of_internal {M : ZFSet.{u}} (hM : M.IsTransitive)
    (ps : Fin 8 → M) (D R F : ZFSet.{u}) (hp : Subtype.val ∘ ps = finiteAdditivityParameters D R F)
    (hadd : finiteAdditivityPredicate.compile.Realize Empty.elim ps)
    (hf : IsFunc D R F) (hv : ∀ C ∈ R, ValidNonnegativeRealCutCode C)
    (he : (∅ : ZFSet.{u}) ∈ D) (hz : pair ∅ ∅ ∈ F)
    (hu : ∀ A ∈ D, ∀ B ∈ D, A ∪ B ∈ D)
    (hd : ∀ A ∈ D, ∀ B ∈ D, A \ B ∈ D) : FiniteAdditiveCutGraph D R F := by
  refine ⟨hf, hv, he, hz, hu, hd, ?_⟩
  intro A hA B hB hdis C E V hAC hBE hUV
  exact finiteAdditivityOnGraph_add hf hu
    ((realize_finiteAdditivityPredicate hM ps D R F hp).mp hadd) hA hB hdis hAC hBE hUV

end PolishSpaceBook.CantorTreeMeasure
