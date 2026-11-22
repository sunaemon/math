module

public import PolishSpaceBook.InternalCohenConditions
public import PolishSpaceBook.BorelInternalCoverTransfer
public import PolishSpaceBook.BorelInternalCodeSelection
public import PolishSpaceBook.BorelInternalCylinderCodes
public import PolishSpaceBook.SetTheoryInternalSequenceSets

@[expose] public section

/-! # Internal Cohen conditions avoiding a coded Borel set

A finite word avoids the internal interpretation when none of its internal
points belongs to that interpretation. Bounded separation collects those words.
Borel inclusion transfer proves that the same word avoids every external point.
-/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure
universe u

/-- The condition is tested only on points in the ground model. -/
def cohenAvoidanceFamily (M : ZFSet.{u}) (c : Code) : Set CohenCondition :=
  {s | ∀ x : ℕ → Bool, cantorPointGraph x ∈ M → x ∈ cyl s → x ∉ c.cantor}

/-- Parameters are the internal set and the proposed finite-word graph. -/
def cohenAvoidancePredicate : BoundedSetPredicate 2 := .all 0 (.neg (.subset 1 2))


/-- The same bounded test applies to an internal set before choosing a Borel representative. -/
def cohenAvoidanceSet (A : ZFSet.{u}) : Set CohenCondition :=
  {s | ∀ g ∈ A, ¬ wordGraph (s.map Bool.toNat) ⊆ g}

lemma binaryWordGraph_subset_pointGraph (s : CohenCondition) (x : ℕ → Bool) :
    wordGraph.{u} (s.map Bool.toNat) ⊆ cantorPointGraph x ↔ x ∈ cyl s := by
  rw [cantorPointGraph, wordGraph_subset_pointGraph]
  change x ∈ cantorInclusion ⁻¹' cyl (s.map Bool.toNat) ↔ _
  rw [BorelExpression.cantorInclusion_preimage_cyl]

lemma eval_cohenAvoidancePredicate (M : ZFSet.{u}) (c : Code) (s : CohenCondition) :
    cohenAvoidancePredicate.eval
      ![internalBorelCantorSet M c.val c.property.2.2.2.2.2, wordGraph (s.map Bool.toNat)] ↔
      s ∈ cohenAvoidanceFamily M c := by
  change (∀ g ∈ internalBorelCantorSet M c.val c.property.2.2.2.2.2,
    ¬ wordGraph (s.map Bool.toNat) ⊆ g) ↔ _
  constructor
  · intro h x hxM hxs hxc
    exact h _ ((cantorPointGraph_mem_internalBorelCantorSet M c.val _ x).mpr ⟨hxM, hxc⟩)
      ((binaryWordGraph_subset_pointGraph s x).mpr hxs)
  · intro h g hg
    obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hg).2
    obtain ⟨hxM, hxc⟩ := (cantorPointGraph_mem_internalBorelCantorSet M c.val _ x).mp hg
    intro hs
    exact h x hxM ((binaryWordGraph_subset_pointGraph s x).mp hs) hxc

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Internal avoiding conditions
-/
include hM hinf hpair hunion hpower hsep in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Bounded separation on $P$ constructs $D_A$ in $M$. Transitivity makes $N(A)$ absolute, so this same family
    is dense externally. The preceding construction gives an internal code for the closed nowhere-dense set
    $\SetDifference{\CantorSpace}{U_{D_A}}$.
    A point of $A$ has no prefix in $D_A$. Conversely, $C(A)$ gives every internal point outside $A$ a prefix in
    $D_A$. Thus this code has internal interpretation exactly $A$.
    For an arbitrary code $a$ with that internal interpretation, membership in $D_A$ means that the cylinder
    contains no internal point of $\BorelValue{a}$. Apply Borel-inclusion transfer to the cylinder code
    and the complement code of $a$, as in the preceding cover lemma.
    The cylinder is disjoint from the full external interpretation as well.
    The reverse implication follows by restriction to internal points.
-/
/-- Separation constructs the whole family from any internal point set. -/
theorem cohenAvoidanceSet_mem (A : ZFSet.{u}) (hA : A ∈ M) :
    cohenConditionSet (cohenAvoidanceSet A) ∈ M := by
  apply cohenAvoidancePredicate.subset_mem hM (hsep _) ![⟨A, hA⟩]
    (binaryWords_mem hM hinf hpair hunion hpower hsep)
  · intro g hg
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hg
    exact mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩
  · intro g hg
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hg
    change s ∈ cohenAvoidanceSet A ↔ _
    constructor
    · intro hs
      exact mem_cohenConditionSet.mpr ⟨s, hs, rfl⟩
    · intro hs
      obtain ⟨t, ht, he⟩ := mem_cohenConditionSet.mp hs
      have hts := (List.map_injective_iff.mpr bool_toNat_injective) (wordGraph_injective he)
      simpa only [hts] using ht

lemma cohenAvoidanceSet_interpretation (M : ZFSet.{u}) (c : Code) :
    cohenAvoidanceSet (internalBorelCantorSet M c.val c.property.2.2.2.2.2) =
      cohenAvoidanceFamily M c := by
  ext s
  exact eval_cohenAvoidancePredicate M c s

include hM hinf hpair hunion hpower hsep in
theorem cohenAvoidanceFamily_mem (c : Code) (hc : c.val.labelGraph ∈ M) :
    cohenConditionSet (cohenAvoidanceFamily M c) ∈ M := by
  rw [← cohenAvoidanceSet_interpretation]
  exact cohenAvoidanceSet_mem hM hinf hpair hunion hpower hsep _
    (internalBorelCantorSet_mem hM hinf hpair hunion hpower hsep c.val c.property.2.2.2.2.2 hc)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Internal avoiding conditions
-/
include hM hinf hpair hunion hpower hsep hrep hchoice in
/-- The bounded test on old points already ensures avoidance at all points. -/
theorem cohenAvoidanceFamily_eq (c : Code) (hc : c.val.labelGraph ∈ M) :
    cohenAvoidanceFamily M c = openCylinderCode c.cantorᶜ := by
  ext s
  constructor
  · intro hs
    have hsub := Code.cantor_subset_of_internal_points hM hinf hpair hunion hpower hsep hrep hchoice
      (Code.binaryCylinder s) c.compl
      (Code.binaryCylinder_labelGraph_mem hM hinf hpair hunion hpower hsep hrep s)
      (Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc) (by
        intro x hxM hxs
        rw [Code.cantor_compl]
        exact hs x hxM (by simpa only [Code.cantor_binaryCylinder] using hxs))
    change cyl s ⊆ c.cantorᶜ
    simpa only [Code.cantor_binaryCylinder, Code.cantor_compl] using hsub
  · intro hs x _ hxs
    exact hs hxs

include hM hinf hpair hunion hpower hsep hrep hchoice in
theorem cohenAvoidanceFamily_dense (c : Code) (hc : c.val.labelGraph ∈ M)
    (hclosed : IsClosed c.cantor) (hnd : IsNowhereDense c.cantor) :
    CohenDense (cohenAvoidanceFamily M c) := by
  rw [cohenAvoidanceFamily_eq hM hinf hpair hunion hpower hsep hrep hchoice c hc]
  obtain ⟨ho, hd⟩ := isClosed_isNowhereDense_iff_compl.mp ⟨hclosed, hnd⟩
  exact cohen_dense_openCylinderCode ho hd

/-- The basis formulation of internal nowhere density; parameters are P and A. -/
def cohenNowhereDensePredicate : BoundedSetPredicate 2 :=
  .all 0 (.ex 0 (.conj (.subset 2 3) (.all 1 (.neg (.subset 3 4)))))

lemma eval_cohenNowhereDensePredicate_set (A : ZFSet.{u}) :
    cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, A] ↔
      CohenDense (cohenAvoidanceSet A) := by
  change (∀ s ∈ cohenConditionSet Set.univ, ∃ t ∈ cohenConditionSet Set.univ,
    s ⊆ t ∧ ∀ g ∈ A, ¬ t ⊆ g) ↔ _
  constructor
  · intro h s
    obtain ⟨t, ht, hst, htg⟩ := h _ (mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩)
    obtain ⟨t, _, rfl⟩ := mem_cohenConditionSet.mp ht
    exact ⟨t, htg, (binaryWordGraph_subset_iff s t).mp hst⟩
  · intro h s hs
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hs
    obtain ⟨t, ht, hts⟩ := h s
    exact ⟨wordGraph (t.map Bool.toNat), mem_cohenConditionSet.mpr ⟨t, Set.mem_univ _, rfl⟩,
      (binaryWordGraph_subset_iff s t).mpr hts, ht⟩

lemma eval_cohenNowhereDensePredicate (M : ZFSet.{u}) (c : Code) :
    cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ,
      internalBorelCantorSet M c.val c.property.2.2.2.2.2] ↔
      CohenDense (cohenAvoidanceFamily M c) := by
  rw [eval_cohenNowhereDensePredicate_set, cohenAvoidanceSet_interpretation]

include hM in
/-- Reflect the model's actual basis assertion to density of the same word family. -/
theorem realize_cohenNowhereDensePredicate (P A : M) (c : Code)
    (hP : P.val = cohenConditionSet Set.univ)
    (hA : A.val = internalBorelCantorSet M c.val c.property.2.2.2.2.2) :
    cohenNowhereDensePredicate.compile.Realize Empty.elim ![P, A] ↔
      CohenDense (cohenAvoidanceFamily M c) := by
  rw [cohenNowhereDensePredicate.realize_compile hM]
  change cohenNowhereDensePredicate.eval ![P.val, A.val] ↔ _
  rw [hP, hA, eval_cohenNowhereDensePredicate]

include hM hinf hpair hunion hpower hsep hrep hchoice in
/-- Genericity meets the internally constructed family, so the point avoids the external interpretation. -/
theorem cohenGeneric_avoids_of_internal_nowhereDense (x : ℕ → Bool)
    (hg : ∀ D : Set CohenCondition, cohenConditionSet D ∈ M → CohenDense D →
      ∃ s ∈ D, x ∈ cyl s)
    (P A : M) (c : Code) (hc : c.val.labelGraph ∈ M)
    (hP : P.val = cohenConditionSet Set.univ)
    (hA : A.val = internalBorelCantorSet M c.val c.property.2.2.2.2.2)
    (hnd : cohenNowhereDensePredicate.compile.Realize Empty.elim ![P, A]) : x ∉ c.cantor := by
  have hd := (realize_cohenNowhereDensePredicate hM P A c hP hA).mp hnd
  obtain ⟨s, hs, hxs⟩ := hg _ (cohenAvoidanceFamily_mem hM hinf hpair hunion hpower hsep c hc) hd
  rw [cohenAvoidanceFamily_eq hM hinf hpair hunion hpower hsep hrep hchoice c hc] at hs
  exact hs hxs


include hM hinf hpair hunion hpower hsep hrep hchoice in
/-- Select a whole code table inside M before transferring an internally witnessed cover. -/
theorem cohenGeneric_avoids_internal_cover (x : ℕ → Bool)
    (hg : ∀ D : Set CohenCondition, cohenConditionSet D ∈ M → CohenDense D →
      ∃ s ∈ D, x ∈ cyl s)
    (c : Code) (hc : c.val.labelGraph ∈ M)
    (V : ℕ → ZFSet.{u}) (hV : sequenceGraph V ∈ M)
    (hex : ∀ n, ∃ (d : BorelExpression) (hd : d.Valid), d.labelGraph ∈ M ∧
      internalBorelCantorSet M d hd.2.2.2.2.2 = V n)
    (hnd : ∀ n, cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, V n])
    (hcover : internalBorelCantorSet M c.val c.property.2.2.2.2.2 ⊆ sequenceUnion V) :
    x ∉ c.cantor := by
  obtain ⟨d, hdM, hdV⟩ := internal_borel_code_sequence hM hinf hpair hunion hpower hsep hrep hchoice V hV hex
  have hdm (n : ℕ) : (d n).val.labelGraph ∈ M :=
    sequence_term_mem hM hunion _ hdM n
  have hav (n : ℕ) : x ∉ (d n).cantor := by
    have hdense : CohenDense (cohenAvoidanceFamily M (d n)) := by
      apply (eval_cohenNowhereDensePredicate M (d n)).mp
      rw [hdV n]
      exact hnd n
    obtain ⟨s, hs, hxs⟩ := hg _
      (cohenAvoidanceFamily_mem hM hinf hpair hunion hpower hsep (d n) (hdm n)) hdense
    rw [cohenAvoidanceFamily_eq hM hinf hpair hunion hpower hsep hrep hchoice (d n) (hdm n)] at hs
    exact hs hxs
  have hfull := Code.cantor_cover_of_internal_points hM hinf hpair hunion hpower hsep hrep hchoice c d hc hdM (by
    intro y hyM hyc
    have hy := hcover ((cantorPointGraph_mem_internalBorelCantorSet M c.val _ y).mpr ⟨hyM, hyc⟩)
    obtain ⟨n, hyn⟩ := (mem_sequenceUnion V _).mp hy
    rw [← hdV n] at hyn
    exact ⟨n, ((cantorPointGraph_mem_internalBorelCantorSet M (d n).val _ y).mp hyn).2⟩)
  intro hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hfull hx)
  exact hav n hn

end PolishSpaceBook
