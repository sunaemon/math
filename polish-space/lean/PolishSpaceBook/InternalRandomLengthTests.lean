module

public import PolishSpaceBook.InternalRandomFilterTransport
public import PolishSpaceBook.ForcingGenericTruth

@[expose] public section

/-! # Internal dense length tests for random forcing -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas BoundedSetPredicate
open BorelExpression MeasureTheory FiniteAdditiveCutGraph ForcingAtomic
universe u

/-- Positive classes below the class of a fixed internal set. -/
def internalNullCone (D F B : ZFSet.{u}) : ZFSet.{u} :=
  (positiveNullQuotient D F).sep (fun C => ∃ A ∈ D,
    pair A C ∈ relationClassMap D (nullRelation D F) ∧ pair (A \ B) ∅ ∈ F)

/-- Parameters: domain, measure graph, quotient map, zero code, target set, candidate class. -/
def internalNullConePredicate : BoundedSetPredicate 6 :=
  .ex 0 (.ex 0 (.conj (.pairMember 2 6 5)
    (.conj (setDifferencePredicate.rename ![6, 4, 7]) (.pairMember 1 7 3))))

lemma eval_internalNullConePredicate {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (B C : ZFSet.{u}) (hB : B ∈ D) :
    internalNullConePredicate.eval ![D, F, relationClassMap D (nullRelation D F), ∅, B, C] ↔
      ∃ A ∈ D, pair A C ∈ relationClassMap D (nullRelation D F) ∧ pair (A \ B) ∅ ∈ F := by
  simp only [internalNullConePredicate, eval, eval_rename, Fin.snoc]
  change (∃ A ∈ D, ∃ U ∈ D, pair A C ∈ relationClassMap D (nullRelation D F) ∧
    setDifferencePredicate.eval ![A, B, U] ∧ pair U ∅ ∈ F) ↔ _
  simp only [eval_setDifferencePredicate]
  constructor
  · rintro ⟨A, hA, U, _, hp, rfl, hz⟩; exact ⟨A, hA, hp, hz⟩
  · rintro ⟨A, hA, hp, hz⟩; exact ⟨A, hA, _, h.diff_mem A hA B hB, hp, rfl, hz⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal order and length tests
-/
include hM hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The quotient map $q$ and the positive condition set $P$ already belong to $M$.
    For $p\in P$, membership in the lower cone has the bounded description
    $$\begin{aligned}
    p\in\InternalMeasureCone{X}\quad\longleftrightarrow\quad
    &\exists A\in D\ \exists U\in D\ \bigl(\langle A,p\rangle\in q\\
    &\qquad{}\land U=\SetDifference{A}{X}\land\langle U,\emptyset\rangle\in F\bigr).
    \end{aligned}$$
    The last clause says that the difference has value zero, since the empty cut code represents zero.
    Closure of the measure domain under differences supplies the intermediate set.
    The comparison theorem identifies this null-difference test with the order on classes.
    The shared bounded predicates for set difference and graph membership therefore give the whole
    lower cone by Separation on $P$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    For the order relation, use the bounded description
    $$\begin{aligned}
    \langle p,r\rangle\in\mathcal O\quad\longleftrightarrow\quad
    &p,r\in P\ \land\ \exists X\in D\ \bigl(\langle X,r\rangle\in q\\
    &\qquad{}\land p\in\InternalMeasureCone{X}\bigr).
    \end{aligned}$$
    Substitute the preceding bounded description for the last membership test and apply Separation
    on $P\times P$. This constructs the entire relation, rather than just its individual ordered pairs.
    Finally,
    $$\InternalRandomLength{M}{n}
    =\bigcup_{s\in\funcspace{n}{2}}\InternalMeasureCone{\InternalCylinder{M}{s}}.$$
    There are finitely many words of this length, and every corresponding cylinder belongs to $D$.
    Each cone is therefore internal, and closure under finite unions puts their union in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    §{sec:internal-finite-measure-laws}. The order relation $\mathcal O$ and all lower cones
    $\InternalMeasureCone{B}$ belong to $M$.
-/
lemma internalNullCone_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val)
    (B : ZFSet.{u}) (hB : B ∈ D.val) : internalNullCone D.val F.val B ∈ M := by
  let q : M := ⟨_, (nullQuotient_mem hM hpair hunion hpower hsep hrep D F h).1⟩
  let Z : M := ⟨∅, hM.mem_trans h.empty_mem D.property⟩
  let b : M := ⟨B, hM.mem_trans hB D.property⟩
  apply internalNullConePredicate.subset_mem hM (hsep _) ![D, F, q, Z, b]
    (B := internalNullCone D.val F.val B)
    (positiveNullQuotient_mem hM hpair hunion hpower hsep hrep D F h)
    (fun _ hc => (ZFSet.mem_sep.mp hc).1)
  intro C hC
  have he : Fin.snoc (Subtype.val ∘ ![D, F, q, Z, b]) C =
      ![D.val, F.val, relationClassMap D.val (nullRelation D.val F.val), ∅, B, C] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_internalNullConePredicate h B C hB]
  simp only [internalNullCone, ZFSet.mem_sep, hC, true_and]

/-- A finite union of internally constructed lower cones. -/
def internalLengthSet (M D F : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  listUnion ((levelCylinderList M Set.univ n).map (internalNullCone D F))

lemma mem_internalLengthSet (M D F C : ZFSet.{u}) (n : ℕ) :
    C ∈ internalLengthSet M D F n ↔
      ∃ s : Fin n → Bool, C ∈ internalNullCone D F (internalWordCylinder M (List.ofFn s)) := by
  classical
  simp [internalLengthSet, mem_listUnion, levelCylinderList, level]

lemma internalLengthSet_subset (M D F : ZFSet.{u}) (n : ℕ) :
    internalLengthSet M D F n ⊆ positiveNullQuotient D F := by
  intro C hC
  obtain ⟨s, hs⟩ := (mem_internalLengthSet M D F C n).mp hC
  exact (ZFSet.mem_sep.mp hs).1

include hM hinf hpair hunion in
lemma listUnion_mem_model (l : List ZFSet.{u}) (hl : ∀ A ∈ l, A ∈ M) : listUnion l ∈ M := by
  induction l with
  | nil => exact empty_mem_of_infinity hM hinf
  | cons A l ih =>
    exact binaryUnion_mem hM hpair hunion (hl A (by simp)) (ih (fun B hB => hl B (by simp [hB])))

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal order and length tests
-/
include hM hinf hpair hunion hpower hsep hrep in
lemma internalLengthSet_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val)
    (hcyl : ∀ s, internalWordCylinder M s ∈ D.val) (n : ℕ) : internalLengthSet M D.val F.val n ∈ M := by
  apply listUnion_mem_model hM hinf hpair hunion
  intro C hC
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hC
  have hBD := ((forall_levelCylinderList M Set.univ n (fun A => A ∈ D.val)).mpr
    (fun s _ => hcyl (List.ofFn s))) B hB
  exact internalNullCone_mem hM hpair hunion hpower hsep hrep D F h B hBD

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)

include h hle in
lemma mem_internalNullCone_iff (B : D) (p : InternalRandomCondition D F η) :
    p.val ∈ internalNullCone D F B.val ↔ η (internalConditionClass η p) ≤ η (nullClassOf (F := F) B) := by
  rw [internalNullCone, ZFSet.mem_sep, and_iff_right p.property]
  constructor
  · rintro ⟨A, hA, hp, hz⟩
    have he : nullClassOf (F := F) ⟨A, hA⟩ = internalConditionClass η p :=
      Subtype.ext ((pair_mem_relationClassMap D (nullRelation D F) ⟨A, hA⟩ p.val).mp hp)
    rw [← he, hle]
    exact (h.pair_zero_iff (h.diff_mem A hA B.val B.property)).mp hz
  · intro hp
    let A := nullClassRepresentative (internalConditionClass η p)
    have he : nullClassOf (F := F) A = internalConditionClass η p :=
      Subtype.ext (nullClassRepresentative_spec _)
    refine ⟨A.val, A.property, (pair_mem_relationClassMap _ _ A _).mpr
      (nullClassRepresentative_spec _), ?_⟩
    apply (h.pair_zero_iff (h.diff_mem A.val A.property B.val B.property)).mpr
    exact (hle A B).mp (he.symm ▸ hp)

/-- The entire coded order, assembled from the same bounded lower-cone test. -/
def internalNullOrder (D F : ZFSet.{u}) : ZFSet.{u} :=
  let P := positiveNullQuotient D F
  (prod P P).sep (fun z => ∃ p ∈ P, ∃ q ∈ P, ∃ B ∈ D,
    z = pair p q ∧ pair B q ∈ relationClassMap D (nullRelation D F) ∧ p ∈ internalNullCone D F B)

def internalNullOrderPredicate : BoundedSetPredicate 6 :=
  .ex 4 (.ex 4 (.ex 0 (.conj (.orderedPair 5 6 7)
    (.conj (.pairMember 2 8 7) (internalNullConePredicate.rename ![0, 1, 2, 3, 8, 6])))))

lemma eval_internalNullOrderPredicate {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (z : ZFSet.{u}) :
    internalNullOrderPredicate.eval ![D, F, relationClassMap D (nullRelation D F), ∅, positiveNullQuotient D F, z] ↔
      z ∈ internalNullOrder D F := by
  simp only [internalNullOrderPredicate, eval, eval_rename, Fin.snoc]
  change (∃ p ∈ positiveNullQuotient D F, ∃ q ∈ positiveNullQuotient D F, ∃ B ∈ D,
    z = pair p q ∧ pair B q ∈ relationClassMap D (nullRelation D F) ∧
      internalNullConePredicate.eval ![D, F, relationClassMap D (nullRelation D F), ∅, B, p]) ↔ _
  rw [internalNullOrder, ZFSet.mem_sep]
  constructor
  · rintro ⟨p, hp, q, hq, B, hB, rfl, hBq, hc⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp, hq⟩, p, hp, q, hq, B, hB, rfl, hBq,
      ZFSet.mem_sep.mpr ⟨hp, (eval_internalNullConePredicate h B p hB).mp hc⟩⟩
  · intro hz
    obtain ⟨_, p, hp, q, hq, B, hB, rfl, hBq, hc⟩ := hz
    exact ⟨p, hp, q, hq, B, hB, rfl, hBq,
      (eval_internalNullConePredicate h B p hB).mpr (ZFSet.mem_sep.mp hc).2⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal order and length tests
-/
include hM hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    §{sec:internal-finite-measure-laws}. The order relation $\mathcal O$ and all lower cones
    $\InternalMeasureCone{B}$ belong to $M$.
-/
lemma internalNullOrder_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val) :
    internalNullOrder D.val F.val ∈ M := by
  let q : M := ⟨_, (nullQuotient_mem hM hpair hunion hpower hsep hrep D F h).1⟩
  let Z : M := ⟨∅, hM.mem_trans h.empty_mem D.property⟩
  let P : M := ⟨_, positiveNullQuotient_mem hM hpair hunion hpower hsep hrep D F h⟩
  apply internalNullOrderPredicate.subset_mem hM (hsep _) ![D, F, q, Z, P]
    (B := internalNullOrder D.val F.val)
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) P.property P.property)
    (by intro z hz; unfold internalNullOrder at hz; exact (ZFSet.mem_sep.mp hz).1)
  intro z _
  have he : Fin.snoc (Subtype.val ∘ ![D, F, q, Z, P]) z =
      ![D.val, F.val, relationClassMap D.val (nullRelation D.val F.val), ∅, positiveNullQuotient D.val F.val, z] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_internalNullOrderPredicate h]

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal order and length tests
-/
include h hle in
lemma pair_mem_internalNullOrder (p q : InternalRandomCondition D F η) :
    pair p.val q.val ∈ internalNullOrder D F ↔ p ≤ q := by
  rw [internalNullOrder, ZFSet.mem_sep, ZFSet.pair_mem_prod, and_iff_right ⟨p.property, q.property⟩]
  constructor
  · rintro ⟨p', _, q', _, B, hB, he, hBq, hc⟩
    obtain ⟨hp, hq⟩ := ZFSet.pair_inj.mp he
    subst p'; subst q'
    have heB : nullClassOf (F := F) ⟨B, hB⟩ = internalConditionClass η q :=
      Subtype.ext ((pair_mem_relationClassMap _ _ ⟨B, hB⟩ _).mp hBq)
    have hle' := (mem_internalNullCone_iff h η hle ⟨B, hB⟩ p).mp hc
    change η (internalConditionClass η p) ≤ η (internalConditionClass η q)
    rw [← heB]
    exact hle'
  · intro hpq
    let B := nullClassRepresentative (internalConditionClass η q)
    have heB : nullClassOf (F := F) B = internalConditionClass η q := Subtype.ext (nullClassRepresentative_spec _)
    exact ⟨p.val, p.property, q.val, q.property, B.val, B.property, rfl,
      (pair_mem_relationClassMap _ _ B _).mpr (nullClassRepresentative_spec _),
      (mem_internalNullCone_iff h η hle B p).mpr (heB.symm ▸ hpq)⟩

variable (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
  pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)

include h hle in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For each $n\in\omega$, define the internal length requirement by
    $$\InternalRandomLength{M}{n}:=
    \{p\in P:\exists s\in\funcspace{n}{2}\ (p\le q(\InternalCylinder{M}{s}))\}.$$
    We now construct these sets inside the model and prove their density.
-/
lemma mem_internalLengthSet_iff (p : InternalRandomCondition D F η) (n : ℕ) :
    p.val ∈ internalLengthSet M D F n ↔ p ∈ internalRandomLengthRequirement η h hcyl n := by
  rw [mem_internalLengthSet]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨List.ofFn s, List.length_ofFn,
      (mem_internalNullCone_iff h η hle ⟨_, (hcyl _).1⟩ p).mp hs⟩
  · rintro ⟨s, hs, hp⟩
    subst n
    refine ⟨fun i => s[i], ?_⟩
    have he : List.ofFn (fun i : Fin s.length => s[i]) = s := by simp
    rw [he]
    exact (mem_internalNullCone_iff h η hle ⟨_, (hcyl _).1⟩ p).mpr hp

namespace FiniteAdditiveCutGraph

lemma inter_mem {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D) : A ∩ B ∈ D := by
  have he : A ∩ B = A \ (A \ B) := by ext x; simp only [ZFSet.mem_inter, ZFSet.mem_sdiff]; tauto
  rw [he]
  exact h.diff_mem _ hA _ (h.diff_mem _ hA _ hB)

lemma exists_positive_of_listUnion {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (l : List ZFSet.{u}) (hl : ∀ A ∈ l, A ∈ D) (hp : 0 < h.value (listUnion l)) :
    ∃ A ∈ l, 0 < h.value A := by
  induction l with
  | nil => simp only [listUnion, h.value_zero, lt_self_iff_false] at hp
  | cons A l ih =>
    have hA := hl A (by simp)
    have htail : ∀ B ∈ l, B ∈ D := fun B hB => hl B (by simp [hB])
    have hle := h.value_union_le hA (h.listUnion_mem l htail)
    change 0 < h.value (A ∪ listUnion l) at hp
    by_cases ha : 0 < h.value A
    · exact ⟨A, by simp, ha⟩
    · have ht : 0 < h.value (listUnion l) := by linarith
      obtain ⟨B, hB, hb⟩ := ih htail ht
      exact ⟨B, by simp [hB], hb⟩

end FiniteAdditiveCutGraph

lemma listUnion_inter_level (M A : ZFSet.{u}) (n : ℕ) (hA : A ⊆ internalCantor M) :
    listUnion ((levelCylinderList M Set.univ n).map (fun B => A ∩ B)) = A := by
  ext g
  rw [mem_listUnion]
  constructor
  · rintro ⟨C, hC, hg⟩
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hC
    exact (ZFSet.mem_inter.mp hg).1
  · intro hg
    obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp (hA hg)
    let s : Fin n → Bool := fun i => x i
    refine ⟨A ∩ internalWordCylinder M (List.ofFn s), List.mem_map.mpr ⟨_, ?_, rfl⟩,
      ZFSet.mem_inter.mpr ⟨hg, (cantorPointGraph_mem_internalWordCylinder M _ x).mpr
        ⟨hxM, mem_cyl_seqPrefix x n⟩⟩⟩
    classical
    simp [levelCylinderList, level]

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Density of internal length tests
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Take $p=q(A)\in P$, so $\nu(A)>0$.
    The Borel representation assumption puts every member of $D$ inside $Y_M$.
    The internal cylinders of length $n$ partition $Y_M$, and hence
    $$A=\bigcup_{s\in\funcspace{n}{2}}\bigl(A\cap\InternalCylinder{M}{s}\bigr).$$
    Each intersection belongs to $D$, since
    $$A\cap B=\SetDifference{A}{(\SetDifference{A}{B})}.$$
    If every intersection had value zero, finite subadditivity and nonnegativity would give $\nu(A)=0$.
    Choose a word $s$ for which the intersection has positive value and set
    $$r:=q(A\cap\InternalCylinder{M}{s}).$$
    Then $r\in P$, $r\le p$, and $r\le q(\InternalCylinder{M}{s})$, proving density.
    The two order inequalities follow because the corresponding differences are empty.
    Transitivity of the order shows closure under further strengthening.
-/
lemma internalRandomLengthRequirement_lower (n : ℕ) :
    IsLowerSet (internalRandomLengthRequirement η h hcyl n) := by
  rintro p q hqp ⟨s, hs, hp⟩
  exact ⟨s, hs, hqp.trans hp⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Density of internal length tests
-/
include h hle in
lemma internalRandomLengthRequirement_dense (hdom : ∀ A ∈ D, A ⊆ internalCantor M) (n : ℕ) :
    IsCoinitial (internalRandomLengthRequirement η h hcyl n) := by
  intro p
  let A := nullClassRepresentative (internalConditionClass η p)
  have he : relationClass D (nullRelation D F) A.val = p.val := nullClassRepresentative_spec _
  have hp : 0 < h.value A.val :=
    (class_mem_positiveNullQuotient_iff h A).mp (he.symm ▸ p.property)
  let l := (levelCylinderList M Set.univ n).map (fun B => A.val ∩ B)
  have hl : ∀ C ∈ l, C ∈ D := by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hC
    exact h.inter_mem A.property
      (((forall_levelCylinderList M Set.univ n (fun B => B ∈ D)).mpr (fun s _ => (hcyl _).1)) B hB)
  have hpos : 0 < h.value (listUnion l) := by
    rw [show listUnion l = A.val from listUnion_inter_level M A.val n (hdom A.val A.property)]
    exact hp
  obtain ⟨C, hCl, hCpos⟩ := h.exists_positive_of_listUnion l hl hpos
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hCl
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hB
  let C : D := ⟨A.val ∩ internalWordCylinder M (List.ofFn s), hl _ hCl⟩
  let q : InternalRandomCondition D F η := ⟨(nullClassOf (F := F) C).val,
    (class_mem_positiveNullQuotient_iff h C).mpr hCpos⟩
  have below (B : D) (hCB : C.val ⊆ B.val) : η (nullClassOf (F := F) C) ≤ η (nullClassOf (F := F) B) := by
    apply (hle C B).mpr
    have hz : C.val \ B.val = ∅ := by
      ext x; simp only [ZFSet.mem_sdiff, ZFSet.notMem_empty, iff_false, not_and]; exact fun hx hn => hn (hCB hx)
    rw [hz, h.value_zero]
  refine ⟨q, ⟨List.ofFn s, List.length_ofFn, below ⟨_, (hcyl _).1⟩ (fun _ hx => (ZFSet.mem_inter.mp hx).2)⟩, ?_⟩
  change η (nullClassOf (F := F) C) ≤ η (internalConditionClass η p)
  have hAc : nullClassOf (F := F) A = internalConditionClass η p := Subtype.ext he
  rw [← hAc]
  exact below A (fun _ hx => (ZFSet.mem_inter.mp hx).1)

/-- The same order on the canonical set-coded condition type used by forcing semantics. -/
@[reducible] def internalConditionCodedOrder : Preorder (Condition (positiveNullQuotient D F)) :=
  Preorder.lift (fun p => η ⟨p.val, (ZFSet.mem_sep.mp p.property).1⟩)

def internalConditionCoding : @OrderIso (InternalRandomCondition D F η)
    (Condition (positiveNullQuotient D F)) inferInstance (internalConditionCodedOrder η).toLE where
  toFun p := ⟨p.val, p.property⟩
  invFun p := ⟨p.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def codedRandomFilter (G : Order.PFilter (InternalRandomCondition D F η)) :
    @Order.PFilter (Condition (positiveNullQuotient D F)) (internalConditionCodedOrder η) := by
  letI := internalConditionCodedOrder η
  exact transportPFilter (internalConditionCoding η).toOrderEmbedding G

include hM hinf hpair hunion hpower hsep hrep h hle in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For an $M$-generic filter $G$, the internal length tests belong to $M$ and are dense in $P$, as proved in
    §{sec:internal-random-filter-valuation}. Thus genericity supplies the length hypothesis, and the valuation
    identity above holds for every such generic filter.
-/
lemma modelGeneric_meets_internalLength (hD : D ∈ M) (hF : F ∈ M)
    (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ∀ n, ∃ p ∈ G, p ∈ internalRandomLengthRequirement η h hcyl n := by
  let := internalConditionCodedOrder η
  intro n
  have hd : IsCoinitial {p : Condition (positiveNullQuotient D F) | p.val ∈ internalLengthSet M D F n} := by
    intro p
    obtain ⟨q, hq, hqp⟩ := internalRandomLengthRequirement_dense h η hle hcyl hdom n
      ((internalConditionCoding η).symm p)
    refine ⟨internalConditionCoding η q, (mem_internalLengthSet_iff h η hle hcyl q n).mpr hq, ?_⟩
    exact (internalConditionCoding η).monotone hqp
  obtain ⟨p, hp, hpn⟩ := hG (internalLengthSet M D F n)
    (internalLengthSet_mem hM hinf hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h (fun s => (hcyl s).1) n)
    (internalLengthSet_subset M D F n) hd
  let q := (internalConditionCoding η).symm p
  have hq : q ∈ G := (image_mem_transportPFilter (internalConditionCoding η).toOrderEmbedding G q).mp hp
  exact ⟨q, hq, (mem_internalLengthSet_iff h η hle hcyl q n).mp hpn⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: The random-real name in a generic extension
-/
include hM hinf hpair hunion hpower hsep hrep h hle hcyl in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Each internal length test is dense and belongs to $M$, so genericity makes $G$ meet it.
    The valuation theorem and its extension-membership corollary now apply.
-/
theorem modelGeneric_randomReal (hD : D ∈ M) (hF : F ∈ M)
    (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (hη : Function.Injective η) (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
    (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
      RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ∃ x : ℕ → Bool,
      (∀ s, x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos) G) ∧
      ForcingNames.valuation (internalFilterSet η G) (randomRealName M D F) = cantorPointGraph x ∧
      cantorPointGraph x ∈ ForcingNames.extension (positiveNullQuotient D F) M (internalFilterSet η G) := by
  have hlen := modelGeneric_meets_internalLength hM hinf hpair hunion hpower hsep hrep h η hle hcyl hD hF hdom G hG
  have hext := transportedRandomFilter_length η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet G hlen
  refine ⟨randomFilterReal _ hext, fun s => randomCoinFilterReal_mem_cyl _ hext s, ?_, ?_⟩
  · exact valuation_randomRealName_eq_filterReal η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet G hlen
  · exact filterReal_graph_mem_extension η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet hrep hD hF G hlen

end PolishSpaceBook.CantorTreeMeasure
