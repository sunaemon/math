module

public import PolishSpaceBook.CantorInternalFiniteApproximation
public import PolishSpaceBook.CantorInternalMeasureBorelValues
public import PolishSpaceBook.InternalNullQuotients

@[expose] public section

/-! # Faithful comparison of internal null classes with the external measure algebra -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

/-- A set of old point graphs represented by a full external set. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A,B\in\mathcal R_M$ be measurable, and let $X,Y\in D$ be subsets of $Y_M$ with
    $$\begin{aligned}
    g_{i(x)}\in X&\quad\longleftrightarrow\quad g_{i(x)}\in M\land x\in A,\\
    g_{i(x)}\in Y&\quad\longleftrightarrow\quad g_{i(x)}\in M\land x\in B.
    \end{aligned}$$
    Thus the internal sets contain exactly the old point graphs lying in the corresponding external
    sets. Write
-/
def RepresentsInternalSet (M X : ZFSet.{u}) (A : Set (ℕ → Bool)) : Prop :=
  X ⊆ internalCantor M ∧ ∀ x, cantorPointGraph x ∈ X ↔ cantorPointGraph x ∈ M ∧ x ∈ A

lemma RepresentsInternalSet.diff {M X Y : ZFSet.{u}} {A B : Set (ℕ → Bool)}
    (hx : RepresentsInternalSet M X A) (hy : RepresentsInternalSet M Y B) :
    RepresentsInternalSet M (X \ Y) (A \ B) := by
  refine ⟨fun _ hz => hx.1 (ZFSet.mem_sdiff.mp hz).1, ?_⟩
  intro x
  simp only [ZFSet.mem_sdiff, hx.2 x, hy.2 x, Set.mem_sdiff]
  tauto

lemma representsInternalBorelCantorSet (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child) :
    RepresentsInternalSet M (internalBorelCantorSet M c hw) (cantorSet c hw) :=
  ⟨fun _ hx => (ZFSet.mem_inter.mp hx).2, cantorPointGraph_mem_internalBorelCantorSet M c hw⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (hY : internalCantor M ∈ D) (hunit : h.value (internalCantor M) = 1)
  (hclosed : ∀ T : Set (List Bool), IsSubtree T → wordTreeSet (binaryLift T) ∈ M →
    internalLevelIntersection M T ∈ D ∧ h.value (internalLevelIntersection M T) = fairCoinProduct.real (treeBody T))

include hM hinf hpair hunion hpower hsep h hY hunit hclosed in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The difference of the internal sets belongs to the measure domain by its finite closure laws.
    The point-membership characterization passes to differences, and the preceding lemma supplies
    internal approximations of the external difference. Apply the squeezing argument of
    §{sec:internal-borel-measure-identification}; its closed-value hypothesis is supplied uniformly by
    §{sec:internal-finite-measure-laws}. This proves the measure identity without constructing a
    new difference code.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The external measure-algebra order is inclusion modulo a null difference. Since the measure is
    finite, vanishing of its real value is equivalent to vanishing of its measure value. This gives the
    order equivalence. Apply it in both directions and use the internal null-class criterion to obtain
    the equality equivalence. Finally, the same squeezing theorem gives $\nu(X)=\mu(A)$.
    Nonnegativity and the characterization of the zero measure class give the positivity equivalence.
-/
lemma value_diff_of_representatives {X Y : ZFSet.{u}} {A B : Set (ℕ → Bool)}
    (hX : X ∈ D) (hY' : Y ∈ D) (hx : RepresentsInternalSet M X A) (hy : RepresentsInternalSet M Y B)
    (ha : InternallyApproximable M A) (hb : InternallyApproximable M B) :
    h.value (X \ Y) = fairCoinProduct.real (A \ B) :=
  value_eq_of_internal_approximations hM hinf hpair hunion hpower hsep h
    (h.diff_mem X hX Y hY') hY hunit (hx.diff hy).1 (hx.diff hy).2
    (internallyApproximable_diff hM hinf hpair hunion hpower hsep ha hb) hclosed

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Faithful comparison of internal measure classes
-/
include hM hinf hpair hunion hpower hsep h hY hunit hclosed in
theorem external_mk_le_iff {X Y : ZFSet.{u}} {A B : Set (ℕ → Bool)}
    (hX : X ∈ D) (hY' : Y ∈ D) (hx : RepresentsInternalSet M X A) (hy : RepresentsInternalSet M Y B)
    (ha : InternallyApproximable M A) (hb : InternallyApproximable M B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (MeasureAlgebra.mk A hmA : MeasureAlgebra fairCoinProduct) ≤ MeasureAlgebra.mk B hmB ↔ h.value (X \ Y) = 0 := by
  rw [MeasureAlgebra.mk_le_mk_iff_null_sdiff,
    value_diff_of_representatives hM hinf hpair hunion hpower hsep h hY hunit hclosed hX hY' hx hy ha hb]
  exact (measureReal_eq_zero_iff (μ := fairCoinProduct)).symm

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Faithful comparison of internal measure classes
-/
include hM hinf hpair hunion hpower hsep h hY hunit hclosed in
theorem external_mk_eq_iff {X Y : ZFSet.{u}} {A B : Set (ℕ → Bool)}
    (hX : X ∈ D) (hY' : Y ∈ D) (hx : RepresentsInternalSet M X A) (hy : RepresentsInternalSet M Y B)
    (ha : InternallyApproximable M A) (hb : InternallyApproximable M B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (MeasureAlgebra.mk A hmA : MeasureAlgebra fairCoinProduct) = MeasureAlgebra.mk B hmB ↔
      relationClass D (nullRelation D F) X = relationClass D (nullRelation D F) Y := by
  rw [le_antisymm_iff, external_mk_le_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed hX hY' hx hy ha hb hmA hmB,
    external_mk_le_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed hY' hX hy hx hb ha hmB hmA,
    nullClass_eq_iff h ⟨X, hX⟩ ⟨Y, hY'⟩]

include hM hinf hpair hunion hpower hsep h hY hunit hclosed in
lemma external_mk_ne_bot_iff {X : ZFSet.{u}} {A : Set (ℕ → Bool)} (hX : X ∈ D)
    (hx : RepresentsInternalSet M X A) (ha : InternallyApproximable M A) (hmA : MeasurableSet A) :
    (MeasureAlgebra.mk A hmA : MeasureAlgebra fairCoinProduct) ≠ ⊥ ↔ 0 < h.value X := by
  rw [ne_eq, MeasureAlgebra.mk_eq_bot,
    value_eq_of_internal_approximations hM hinf hpair hunion hpower hsep h hX hY hunit hx.1 hx.2 ha hclosed]
  rw [← measureReal_eq_zero_iff (μ := fairCoinProduct)]
  exact ⟨fun hn => lt_of_le_of_ne measureReal_nonneg (Ne.symm hn), ne_of_gt⟩


/-- Select a carrier element from a set-coded equivalence class. -/
def nullClassRepresentative (C : relationQuotient D (nullRelation D F)) : D :=
  ⟨Classical.choose ((mem_relationQuotient _ _ _).mp C.property),
    (Classical.choose_spec ((mem_relationQuotient _ _ _).mp C.property)).1⟩

lemma nullClassRepresentative_spec (C : relationQuotient D (nullRelation D F)) :
    relationClass D (nullRelation D F) (nullClassRepresentative C).val = C.val :=
  (Classical.choose_spec ((mem_relationQuotient _ _ _).mp C.property)).2

def nullClassOf (A : D) : relationQuotient D (nullRelation D F) :=
  ⟨relationClass D (nullRelation D F) A.val,
    (mem_relationQuotient _ _ _).mpr ⟨A.val, A.property, rfl⟩⟩

/-- An external measure-algebra image; no internal selection of representatives is asserted. -/
def measureClassImage (S : D → Set (ℕ → Bool)) (hS : ∀ A, MeasurableSet (S A))
    (C : relationQuotient D (nullRelation D F)) : MeasureAlgebra fairCoinProduct :=
  MeasureAlgebra.mk (S (nullClassRepresentative C)) (hS _)

variable (S : D → Set (ℕ → Bool)) (hmS : ∀ A, MeasurableSet (S A))
  (haS : ∀ A, InternallyApproximable M (S A))
  (hpS : ∀ A, RepresentsInternalSet M A.val (S A))

include hM hinf hpair hunion hpower hsep h hY hunit hclosed haS hpS in
lemma measureClassImage_of (A : D) :
    measureClassImage S hmS (nullClassOf (F := F) A) = MeasureAlgebra.mk (S A) (hmS A) := by
  let C := nullClassOf (F := F) A
  let B := nullClassRepresentative C
  exact (external_mk_eq_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed
    B.property A.property (hpS B) (hpS A) (haS B) (haS A) (hmS B) (hmS A)).mpr
      (nullClassRepresentative_spec C)

include hM hinf hpair hunion hpower hsep h hY hunit hclosed haS hpS in
lemma measureClassImage_of_representative (X : D) {A : Set (ℕ → Bool)}
    (hmA : MeasurableSet A) (haA : InternallyApproximable M A) (hpA : RepresentsInternalSet M X.val A) :
    measureClassImage S hmS (nullClassOf (F := F) X) = MeasureAlgebra.mk A hmA := by
  rw [measureClassImage_of hM hinf hpair hunion hpower hsep h hY hunit hclosed S hmS haS hpS X]
  exact (external_mk_eq_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed
    X.property X.property (hpS X) hpA (haS X) haA (hmS X) hmA).mpr rfl

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Embedding the internal Borel measure classes
-/
include hM hinf hpair hunion hpower hsep h hY hunit hclosed haS hpS in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Choose a valid internal Borel code for each element of the measure domain, and take its full external
    interpretation. §{sec:internal-approximation-errors} supplies internal two-sided approximations
    for each of these measurable sets. Choose a representative of each internal null class and assign
    the external measure class of the selected interpretation. These choices are made in the ambient
    universe.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The faithful comparison theorem shows that any measurable set with internal approximations and the
    same old-point membership gives the same external class. This proves the stated representative
    identity and independence of the choices. The theorem also shows that equality of the assigned
    external classes forces equality of the internal classes, proving injectivity. Its order and
    positivity criteria give the remaining assertions.
-/
theorem measureClassImage_injective : Function.Injective (measureClassImage (F := F) S hmS) := by
  intro C E he
  let A := nullClassRepresentative C
  let B := nullClassRepresentative E
  have hclass := (external_mk_eq_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed
    A.property B.property (hpS A) (hpS B) (haS A) (haS B) (hmS A) (hmS B)).mp he
  apply Subtype.ext
  exact (nullClassRepresentative_spec C).symm.trans (hclass.trans (nullClassRepresentative_spec E))

include hM hinf hpair hunion hpower hsep h hY hunit hclosed haS hpS in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For $p=q(B')$, the order condition is exactly $\mu(\SetDifference{B'}{\BorelInterpretation{c}{M}})=0$.
    Here $\mu$ denotes the decoded internal measure, whose value agrees with the external measure of the coded set.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Order the internal positive classes by $q(X)\le q(Y)$ if $\nu(\SetDifference{X}{Y})=0$.
    The comparison theorem makes this well-defined and turns the restriction of $\eta$ to $P$ into an
    order embedding into the external positive measure classes $Q_+$.
-/
lemma measureClassImage_le_iff (A B : D) :
    measureClassImage S hmS (nullClassOf (F := F) A) ≤ measureClassImage S hmS (nullClassOf (F := F) B) ↔
      h.value (A.val \ B.val) = 0 := by
  rw [measureClassImage_of hM hinf hpair hunion hpower hsep h hY hunit hclosed S hmS haS hpS A,
    measureClassImage_of hM hinf hpair hunion hpower hsep h hY hunit hclosed S hmS haS hpS B]
  exact external_mk_le_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed
    A.property B.property (hpS A) (hpS B) (haS A) (haS B) (hmS A) (hmS B)

include hM hinf hpair hunion hpower hsep h hY hunit hclosed haS hpS in
lemma measureClassImage_ne_bot_iff (C : relationQuotient D (nullRelation D F)) :
    measureClassImage S hmS C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F := by
  let A := nullClassRepresentative C
  have he := external_mk_ne_bot_iff hM hinf hpair hunion hpower hsep h hY hunit hclosed
    A.property (hpS A) (haS A) (hmS A)
  change measureClassImage S hmS C ≠ ⊥ ↔ 0 < h.value A.val at he
  rw [← nullClassRepresentative_spec C]
  exact he.trans (class_mem_positiveNullQuotient_iff h A).symm

section Borel
variable
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence) (hca : h.ModelsCountableAdditivity M)
  (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
    pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)

/-- Each member of the model's Borel domain is specified by an actual whole code in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now suppose every $X\in D$ is the internal interpretation of a valid Borel code whose entire label
    graph belongs to $M$. This is the representation requirement for using the model's Borel domain;
    finite measure laws alone do not supply Borel codes for its elements.
-/
def HasInternalBorelRepresentatives (M D : ZFSet.{u}) : Prop :=
  ∀ A : D, ∃ c : BorelExpression, ∃ hc : c.Valid,
    c.labelGraph ∈ M ∧ internalBorelCantorSet M c hc.2.2.2.2.2 = A.val

lemma HasInternalBorelRepresentatives.domain_subset (hcodes : HasInternalBorelRepresentatives M D)
    (A : ZFSet.{u}) (hA : A ∈ D) : A ⊆ internalCantor M := by
  obtain ⟨c, hc, _, he⟩ := hcodes ⟨A, hA⟩
  change internalBorelCantorSet M c hc.2.2.2.2.2 = A at he
  rw [← he]
  exact (representsInternalBorelCantorSet M c hc.2.2.2.2.2).1

include hM hinf hpair hunion hpower hsep hrep hchoice in
lemma exists_borelRepresentativeFamily (hcodes : HasInternalBorelRepresentatives M D) :
    ∃ S : D → Set (ℕ → Bool), (∀ A, MeasurableSet (S A)) ∧
      (∀ A, InternallyApproximable M (S A)) ∧ (∀ A, RepresentsInternalSet M A.val (S A)) := by
  choose c hc hcM hcA using hcodes
  exact ⟨fun A => cantorSet (c A) (hc A).2.2.2.2.2,
    fun A => measurableSet_cantorSet (c A) _,
    fun A => internallyApproximable_cantorSet hM hinf hpair hunion hpower hsep hrep hchoice (c A) (hc A) (hcM A),
    fun A => hcA A ▸ representsInternalBorelCantorSet M (c A) _⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Embedding the internal Borel measure classes
-/
include hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl in
theorem exists_measureClassEmbedding (hcodes : HasInternalBorelRepresentatives M D) :
    ∃ η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct,
      Function.Injective η ∧
      (∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0) ∧
      (∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F) ∧
      ∀ (X : D) (A : Set (ℕ → Bool)) (hmA : MeasurableSet A), InternallyApproximable M A →
        RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hmA := by
  obtain ⟨S, hm, ha, hp⟩ := exists_borelRepresentativeFamily hM hinf hpair hunion hpower hsep hrep hchoice hcodes
  have hcl := countableMeasure_closed_values hM hinf hpair hunion hpower hsep hrep h hca hcyl
  refine ⟨measureClassImage S hm,
    measureClassImage_injective hM hinf hpair hunion hpower hsep h hY hunit hcl S hm ha hp,
    measureClassImage_le_iff hM hinf hpair hunion hpower hsep h hY hunit hcl S hm ha hp,
    measureClassImage_ne_bot_iff hM hinf hpair hunion hpower hsep h hY hunit hcl S hm ha hp, ?_⟩
  intro X A hmA haA hpA
  exact measureClassImage_of_representative hM hinf hpair hunion hpower hsep h hY hunit hcl S hm ha hp
    X hmA haA hpA

include hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl in
theorem exists_borelMeasureClassEmbedding (hcodes : HasInternalBorelRepresentatives M D) :
    ∃ η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct,
      Function.Injective η ∧
      (∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0) ∧
      (∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F) ∧
      ∀ (A : D) (c : BorelExpression) (hc : c.Valid), c.labelGraph ∈ M →
        internalBorelCantorSet M c hc.2.2.2.2.2 = A.val →
        η (nullClassOf (F := F) A) = MeasureAlgebra.mk (cantorSet c hc.2.2.2.2.2) (measurableSet_cantorSet c _) := by
  obtain ⟨η, hη, hle, hpos, hrepSet⟩ :=
    exists_measureClassEmbedding hM hinf hpair hunion hpower hsep h hY hunit hrep hchoice hca hcyl hcodes
  refine ⟨η, hη, hle, hpos, ?_⟩
  intro A c hc hcM hcA
  exact hrepSet A _ (measurableSet_cantorSet c _)
    (internallyApproximable_cantorSet hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM)
    (hcA ▸ representsInternalBorelCantorSet M c _)

end Borel

end PolishSpaceBook.CantorTreeMeasure
