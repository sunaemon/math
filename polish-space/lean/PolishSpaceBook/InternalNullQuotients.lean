module

public import PolishSpaceBook.SetTheoryInternalQuotients
public import PolishSpaceBook.SetTheoryInternalSequenceSets
public import PolishSpaceBook.FiniteAdditiveCutGraphs

@[expose] public section

/-! # Internal quotients modulo a coded finite measure's null sets -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas BoundedSetPredicate
universe u

namespace FiniteAdditiveCutGraph
variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

lemma pair_zero_iff {A : ZFSet.{u}} (hA : A ∈ D) : pair A ∅ ∈ F ↔ h.value A = 0 := by
  constructor
  · intro hp
    exact h.value_of_code hA (le_refl 0) (nonnegativeRealCutCode_zero.symm ▸ hp)
  · intro hv
    have he : h.code A = ∅ := (h.code_valid hA).encode_decode.trans
      (by rw [← value, hv, nonnegativeRealCutCode_zero])
    exact he ▸ h.pair_code hA

lemma value_union_le {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D) :
    h.value (A ∪ B) ≤ h.value A + h.value B := by
  have hd : Disjoint (A : Set ZFSet) ((B \ A : ZFSet) : Set ZFSet) := by
    rw [Set.disjoint_left]
    exact fun _ hx hy => (ZFSet.mem_sdiff.mp hy).2 hx
  have he : A ∪ (B \ A) = A ∪ B := by
    ext x
    simp only [ZFSet.mem_union, ZFSet.mem_sdiff]
    tauto
  have hadd := h.value_union hA (h.diff_mem B hB A hA) hd
  rw [he] at hadd
  rw [hadd]
  have hle := h.value_mono (h.diff_mem B hB A hA) hB
    (fun _ hx => (ZFSet.mem_sdiff.mp hx).1)
  linarith

/-- Equality modulo null differences, on the actual internal domain of the measure. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now also assume Power Set in $M$. Let $D,F\in M$ and let $F:D\to R$ satisfy the finite measure laws
    of §{sec:internal-finite-measure-laws}. In particular, $D$ contains $\emptyset$ and is closed under
    finite unions and differences. Let $\nu$ be the decoded value function. Define
    $$E:=\{\langle A,B\rangle\in D\times D:
    \nu(\SetDifference{A}{B})=0=\nu(\SetDifference{B}{A})\}.$$
    This is equality modulo null differences.
-/
def nullEquivalent (A B : ZFSet.{u}) : Prop := h.value (A \ B) = 0 ∧ h.value (B \ A) = 0

lemma nullEquivalent_refl (A : ZFSet.{u}) : h.nullEquivalent A A := by
  have he : A \ A = ∅ := by ext x; simp
  simp only [nullEquivalent, he, h.value_zero, and_self]

lemma nullEquivalent_symm {A B : ZFSet.{u}} (hab : h.nullEquivalent A B) : h.nullEquivalent B A :=
  hab.symm

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Reflexivity and symmetry follow immediately from the zero law and the definition. For transitivity,
    finite additivity applied to a disjoint decomposition gives
    $$\nu(A\cup B)=\nu(A)+\nu(\SetDifference{B}{A})\le\nu(A)+\nu(B).$$
    Combine this with
    $$\SetDifference{A}{C}\IncludedIn
    (\SetDifference{A}{B})\cup(\SetDifference{B}{C})$$
    and monotonicity. If both differences on the right have value zero, nonnegativity forces the left
    one to have value zero. Interchanging the first and third sets gives the reverse difference.
    The preceding theorem now constructs the quotient map and quotient set. The empty-set class belongs
    to the model, so a further bounded Separation gives the positive conditions. Finally, equality with
    the empty-set class is equivalent to having value zero; nonnegativity gives the asserted positivity test.
-/
lemma nullEquivalent_trans {A B C : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D) (hC : C ∈ D)
    (hab : h.nullEquivalent A B) (hbc : h.nullEquivalent B C) : h.nullEquivalent A C := by
  have step (A B C : ZFSet.{u}) (hA : A ∈ D) (hB : B ∈ D) (hC : C ∈ D)
      (hab : h.value (A \ B) = 0) (hbc : h.value (B \ C) = 0) : h.value (A \ C) = 0 := by
    have hsub : A \ C ⊆ (A \ B) ∪ (B \ C) := by
      intro x hx
      simp only [ZFSet.mem_sdiff, ZFSet.mem_union] at *
      tauto
    have hle := (h.value_mono (h.diff_mem A hA C hC)
      (h.union_mem _ (h.diff_mem A hA B hB) _ (h.diff_mem B hB C hC)) hsub).trans
        (h.value_union_le (h.diff_mem A hA B hB) (h.diff_mem B hB C hC))
    rw [hab, hbc, add_zero] at hle
    exact le_antisymm hle (h.value_nonneg (h.diff_mem A hA C hC))
  exact ⟨step A B C hA hB hC hab.1 hbc.1, step C B A hC hB hA hbc.2 hab.2⟩

def nullSetoid : Setoid D where
  r A B := h.nullEquivalent A.val B.val
  iseqv := ⟨fun A => h.nullEquivalent_refl A.val,
    fun hab => h.nullEquivalent_symm hab,
    fun {A B C} hab hbc => h.nullEquivalent_trans A.property B.property C.property hab hbc⟩

end FiniteAdditiveCutGraph

def nullRelation (D F : ZFSet.{u}) : ZFSet.{u} :=
  (prod D D).sep (fun z => ∃ A ∈ D, ∃ B ∈ D, z = pair A B ∧
    pair (A \ B) ∅ ∈ F ∧ pair (B \ A) ∅ ∈ F)

lemma pair_mem_nullRelation (D F A B : ZFSet.{u}) :
    pair A B ∈ nullRelation D F ↔ A ∈ D ∧ B ∈ D ∧ pair (A \ B) ∅ ∈ F ∧ pair (B \ A) ∅ ∈ F := by
  simp only [nullRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨hA, hB⟩, C, _, E, _, ⟨rfl, rfl⟩, hCE, hEC⟩
    exact ⟨hA, hB, hCE, hEC⟩
  · rintro ⟨hA, hB, hAB, hBA⟩
    exact ⟨⟨hA, hB⟩, A, hA, B, hB, ⟨rfl, rfl⟩, hAB, hBA⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now also assume Power Set in $M$. Let $D,F\in M$ and let $F:D\to R$ satisfy the finite measure laws
    of §{sec:internal-finite-measure-laws}. In particular, $D$ contains $\emptyset$ and is closed under
    finite unions and differences. Let $\nu$ be the decoded value function. Define
    $$E:=\{\langle A,B\rangle\in D\times D:
    \nu(\SetDifference{A}{B})=0=\nu(\SetDifference{B}{A})\}.$$
    This is equality modulo null differences.
-/
lemma pair_mem_nullRelation_iff {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (A B : D) :
    pair A.val B.val ∈ nullRelation D F ↔ h.nullSetoid.r A B := by
  rw [pair_mem_nullRelation]
  simp only [A.property, B.property, true_and, h.pair_zero_iff (h.diff_mem _ A.property _ B.property),
    h.pair_zero_iff (h.diff_mem _ B.property _ A.property)]
  rfl

/-- Parameters domain, measure graph, zero code, candidate ordered pair. -/
def nullRelationPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 0 (.conj (.orderedPair 3 4 5)
    (.conj (setDifferencePredicate.rename ![4, 5, 6])
      (.conj (setDifferencePredicate.rename ![5, 4, 7])
        (.conj (.pairMember 1 6 2) (.pairMember 1 7 2))))))))

lemma eval_nullRelationPredicate {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (z : ZFSet.{u}) :
    nullRelationPredicate.eval ![D, F, ∅, z] ↔ z ∈ nullRelation D F := by
  let ps : Fin 4 → ZFSet.{u} := ![D, F, ∅, z]
  have he (A B U V : ZFSet.{u}) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) U) V ∘ ![(4 : Fin 8), 5, 6] = ![A, B, U] := by
    funext i; fin_cases i <;> rfl
  have he' (A B U V : ZFSet.{u}) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) U) V ∘ ![(5 : Fin 8), 4, 7] = ![B, A, V] := by
    funext i; fin_cases i <;> rfl
  change nullRelationPredicate.eval ps ↔ _
  simp only [nullRelationPredicate, eval, eval_rename, he, he', eval_setDifferencePredicate]
  change (∃ A ∈ D, ∃ B ∈ D, ∃ U ∈ D, ∃ V ∈ D,
    z = pair A B ∧ U = A \ B ∧ V = B \ A ∧ pair U ∅ ∈ F ∧ pair V ∅ ∈ F) ↔ _
  constructor
  · rintro ⟨A, hA, B, hB, U, _, V, _, rfl, rfl, rfl, hAB, hBA⟩
    exact (pair_mem_nullRelation D F A B).mpr ⟨hA, hB, hAB, hBA⟩
  · intro hz
    obtain ⟨_, A, hA, B, hB, rfl, hAB, hBA⟩ := ZFSet.mem_sep.mp hz
    exact ⟨A, hA, B, hB, A \ B, h.diff_mem A hA B hB, B \ A, h.diff_mem B hB A hA,
      rfl, rfl, rfl, hAB, hBA⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hpair hunion hpower hsep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The empty cut code represents zero, so for each $U\in D$,
    $$\nu(U)=0\quad\longleftrightarrow\quad\langle U,\emptyset\rangle\in F.$$
    Thus membership of $\langle A,B\rangle$ in the relation is expressed by bounded quantification over
    $U,V\in D$, requiring
    $$\begin{gathered}
    U=\SetDifference{A}{B},\qquad V=\SetDifference{B}{A},\\
    \langle U,\emptyset\rangle\in F,\qquad\langle V,\emptyset\rangle\in F.
    \end{gathered}$$
    The two difference equations use the shared bounded subset predicate. Closure under differences
    supplies the witnesses, and bounded Separation on $D\times D$ gives $E\in M$.
-/
lemma nullRelation_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val) :
    nullRelation D.val F.val ∈ M := by
  let Z : M := ⟨∅, hM.mem_trans h.empty_mem D.property⟩
  apply nullRelationPredicate.subset_mem hM (hsep _) ![D, F, Z]
    (B := nullRelation D.val F.val)
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) D.property D.property)
    (fun _ hz => (ZFSet.mem_sep.mp hz).1)
  intro z _
  have he : Fin.snoc (Subtype.val ∘ ![D, F, Z]) z = ![D.val, F.val, ∅, z] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_nullRelationPredicate h]

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal null quotients
-/
include hM hpair hunion hpower hsep hrep in
theorem nullQuotient_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val) :
    relationClassMap D.val (nullRelation D.val F.val) ∈ M ∧
      relationQuotient D.val (nullRelation D.val F.val) ∈ M := by
  let E : M := ⟨_, nullRelation_mem hM hpair hunion hpower hsep D F h⟩
  exact ⟨relationClassMap_mem hM hpair hsep hrep D E,
    relationQuotient_mem hM hpair hunion hsep hrep D E⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal null quotients
-/
theorem nullClass_eq_iff {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (A B : D) :
    relationClass D (nullRelation D F) A.val = relationClass D (nullRelation D F) B.val ↔
      h.value (A.val \ B.val) = 0 ∧ h.value (B.val \ A.val) = 0 :=
  relationClass_eq_iff D (nullRelation D F) h.nullSetoid (pair_mem_nullRelation_iff h) A B


/-- Positive conditions of the internal quotient, excluding the null class. -/
def positiveNullQuotient (D F : ZFSet.{u}) : ZFSet.{u} :=
  (relationQuotient D (nullRelation D F)).sep (fun C => C ≠ relationClass D (nullRelation D F) ∅)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal null quotients
-/
include hM hpair hunion hpower hsep hrep in
theorem positiveNullQuotient_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val) :
    positiveNullQuotient D.val F.val ∈ M := by
  let E : M := ⟨_, nullRelation_mem hM hpair hunion hpower hsep D F h⟩
  let Z : M := ⟨∅, hM.mem_trans h.empty_mem D.property⟩
  let C : M := ⟨_, relationClass_mem hM hsep D E Z⟩
  exact (BoundedSetPredicate.neg (.equal (1 : Fin 2) 0)).separation_mem hM (hsep _) ![C]
    (nullQuotient_mem hM hpair hunion hpower hsep hrep D F h).2

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal null quotients
-/
theorem class_mem_positiveNullQuotient_iff {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (A : D) :
    relationClass D (nullRelation D F) A.val ∈ positiveNullQuotient D F ↔ 0 < h.value A.val := by
  have hm : relationClass D (nullRelation D F) A.val ∈ relationQuotient D (nullRelation D F) :=
    (mem_relationQuotient _ _ _).mpr ⟨A.val, A.property, rfl⟩
  have hd : A.val \ ∅ = A.val := by ext x; simp
  have hd' : (∅ : ZFSet.{u}) \ A.val = ∅ := by ext x; simp
  have he := nullClass_eq_iff h A ⟨∅, h.empty_mem⟩
  change relationClass D (nullRelation D F) A.val = relationClass D (nullRelation D F) ∅ ↔
    h.value (A.val \ ∅) = 0 ∧ h.value (∅ \ A.val) = 0 at he
  rw [hd, hd', h.value_zero] at he
  simp only [positiveNullQuotient, ZFSet.mem_sep, hm, true_and, ne_eq, he, and_true]
  exact ⟨fun hn => lt_of_le_of_ne (h.value_nonneg A.property) (Ne.symm hn), ne_of_gt⟩

end PolishSpaceBook.CantorTreeMeasure
