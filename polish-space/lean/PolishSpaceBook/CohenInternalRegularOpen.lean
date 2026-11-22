module

public import PolishSpaceBook.CohenInternalCompletion
public import PolishSpaceBook.RegularCompletionComparison
public import PolishSpaceBook.ForcingInternalRegularHom

@[expose] public section

/-! # Faithful regular-open interpretation of the internal Cohen completion -/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic SetTheoryModels
universe u

local instance cohenRegularOpenComparisonOrder : PartialOrder (Condition (cohenConditionSet.{u} Set.univ)) :=
  cohenCodePartialOrder

def cohenCodeWord (p : Condition (cohenConditionSet.{u} Set.univ)) : CohenCondition :=
  (cohenCodedCondition_surjective p).choose

lemma cohenCodedCondition_codeWord (p : Condition (cohenConditionSet.{u} Set.univ)) :
    cohenCodedCondition (cohenCodeWord p) = p := (cohenCodedCondition_surjective p).choose_spec

/-- Decode finite function graphs and take their actual Cantor cylinders. -/
def cohenCodeCylinderEmbedding : Condition (cohenConditionSet.{u} Set.univ) ↪o RegularOpen (ℕ → Bool) where
  toFun p := cohenCylinder (cohenCodeWord p)
  inj' := by
    intro p q hpq
    have hs := cohenRegularOpenEmbedding.injective hpq
    rw [← cohenCodedCondition_codeWord p, ← cohenCodedCondition_codeWord q, hs]
  map_rel_iff' := by
    intro p q
    change cohenCylinder (cohenCodeWord p) ≤ cohenCylinder (cohenCodeWord q) ↔ p ≤ q
    rw [cohenCylinder_le_iff, ← cohenCodedCondition_le_iff, cohenCodedCondition_codeWord, cohenCodedCondition_codeWord]

lemma cohenCodeCylinder_ne_bot (p : Condition (cohenConditionSet.{u} Set.univ)) :
    cohenCodeCylinderEmbedding p ≠ ⊥ := cohenCylinder_ne_bot _

lemma cohenCodeCylinder_dense (U : RegularOpen (ℕ → Bool)) (hU : U ≠ ⊥) :
    ∃ p : Condition (cohenConditionSet.{u} Set.univ), cohenCodeCylinderEmbedding p ≤ U := by
  obtain ⟨s, hs⟩ := cohenCylinder_dense U hU
  refine ⟨cohenCodedCondition s, ?_⟩
  have he : cohenCodeWord (cohenCodedCondition.{u} s) = s := by
    apply cohenRegularOpenEmbedding.injective
    apply le_antisymm <;> apply (cohenCylinder_le_iff _ _).mpr
    · exact (cohenCodedCondition_le_iff s _).mp (le_of_eq (cohenCodedCondition_codeWord _))
    · exact (cohenCodedCondition_le_iff _ s).mp (le_of_eq (cohenCodedCondition_codeWord _).symm)
  change cohenCylinder (cohenCodeWord (cohenCodedCondition s)) ≤ U
  rw [he]
  exact hs

/-- External regular lower sets and the usual Cantor regular opens are the
same complete Boolean algebra through the cylinder comparison. -/
def cohenRegularCompletionIso :
    RegularForcingSet (Condition (cohenConditionSet.{u} Set.univ)) ≃o RegularOpen (ℕ → Bool) :=
  regularCompletionIso cohenCodeCylinderEmbedding cohenCodeCylinder_ne_bot cohenCodeCylinder_dense

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

local notation "P" => cohenConditionsInModel hM hinf hpair hunion hpower hsep
local notation "R" => cohenOrderInModel hM hinf hpair hunion hpower hsep
local notation "B" => cohenCompletionCarrier hM hinf hpair hunion hpower hsep
local notation "Alg" => cohenCompletionBooleanAlgebra hM hinf hpair hunion hpower hsep

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compare this construction with regular opens of Cantor space, send a regular lower set $U$ to
    $$J(U)=\bigvee_{p\in U}\cyl{p},$$
    where the join is computed in the external regular-open algebra, by regularizing the union.
    Then $\cyl{p}\IncludedIn J(U)$ holds exactly when $p\in U$.
    Indeed, if $p\notin U$, regularity supplies $q\le p$ with no extension in $U$.
    Its cylinder is disjoint from every cylinder indexed by $U$, and therefore from their regular-open
    join, contradicting $\cyl{p}\IncludedIn J(U)$. The converse follows from the definition of the join.
    The inverse sends a regular open $V$ to $\{p\in P:\cyl{p}\IncludedIn V\}$; density of cylinders
    makes this set regular and recovers $V$ as its join. Thus the external completions are Boolean
    isomorphic. Restricting to internally coded lower sets gives a faithful Boolean representation,
    and $J(e(p))=\cyl{p}$. Completeness of the internal carrier is still required only for families in $M$.
-/
/-- Internal codes are mapped faithfully to external regular opens. No
surjectivity onto all external regular opens is asserted for the internal carrier. -/
def cohenInternalRegularOpenEmbedding :
    letI := Alg
    BooleanElement (B).val ↪o RegularOpen (ℕ → Bool) := by
  letI := Alg
  refine {
    toFun := fun b => cohenRegularCompletionIso (decodeInternalRegular cohenOrderGraph_correct M b)
    inj' := fun _ _ h => decodeInternalRegular_injective cohenOrderGraph_correct M (cohenRegularCompletionIso.injective h)
    map_rel_iff' := ?_ }
  intro a b
  change cohenRegularCompletionIso (decodeInternalRegular cohenOrderGraph_correct M a) ≤
    cohenRegularCompletionIso (decodeInternalRegular cohenOrderGraph_correct M b) ↔ a ≤ b
  rw [OrderIso.le_iff_le]
  change conditionsOfCode (P).val a.val ⊆ conditionsOfCode (P).val b.val ↔ a ≤ b
  rw [internalRegular_le_iff hM hinf hpair hunion hsep P R cohenOrderGraph_correct]
  constructor
  · intro h x hx
    have hxP := ((mem_internalRegularCarrier cohenOrderGraph_correct M a.val).mp a.property).2.1 hx
    exact h (a := ⟨x, hxP⟩) hx
  · intro h p hp; exact h hp

/-- The external regular open is exactly the regularization of the union of
cylinders selected by the internal code. -/
lemma cohenInternalRegularOpen_coe (b : BooleanElement (B).val) :
    letI := Alg
    ((cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep b).val : Set (ℕ → Bool)) =
      interior (closure (⋃ p : Condition (P).val, ⋃ (_ : p.val ∈ b.val),
        cyl (cohenCodeWord p))) := by
  let _ := Alg
  change ((regularComparison cohenCodeCylinderEmbedding
    (decodeInternalRegular cohenOrderGraph_correct M b)).val : Set (ℕ → Bool)) = _
  rw [regularComparison, regularOpen_sSup_coe]
  congr 2
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨U, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨cohenCodeCylinderEmbedding p, ⟨p, hp, rfl⟩, hx⟩

lemma cohenInternalRegularOpen_principal (p : Condition (P).val) :
    letI := Alg
    cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep
      (InternalBooleanAlgebra.element B (cohenCompletionEmbedding hM hinf hpair hunion hpower hsep p)) =
        cohenCodeCylinderEmbedding p := by
  let _ := Alg
  change regularComparison cohenCodeCylinderEmbedding
    (decodeInternalRegular cohenOrderGraph_correct M
      (regularPrincipal hM hpower hsep P R cohenOrderGraph_correct cohenCode_separative p)) = _
  apply le_antisymm
  · apply sSup_le
    rintro c ⟨q, hq, rfl⟩
    apply cohenCodeCylinderEmbedding.monotone
    have hqp : q ∈ conditionsOfCode (P).val (principalConditionCode (P).val (R).val p.val) := hq
    rw [principalConditionCode_correct P R cohenOrderGraph_correct p] at hqp
    exact hqp
  · apply le_sSup
    refine ⟨p, ?_, rfl⟩
    change p ∈ conditionsOfCode (P).val (principalConditionCode (P).val (R).val p.val)
    rw [principalConditionCode_correct P R cohenOrderGraph_correct p]
    exact (show p ≤ p from le_rfl)

lemma cohenInternalRegularOpen_inf (a b : BooleanElement (B).val) :
    letI := Alg
    cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep (a ⊓ b) =
      cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep a ⊓
        cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep b := by
  let _ := Alg
  change cohenRegularCompletionIso (decodeInternalRegular cohenOrderGraph_correct M (a ⊓ b)) = _
  rw [decodeInternalRegular_inf hM hinf hpair hunion hsep P R cohenOrderGraph_correct, OrderIso.map_inf]
  rfl

lemma cohenInternalRegularOpen_compl (a : BooleanElement (B).val) :
    letI := Alg
    cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep aᶜ =
      (cohenInternalRegularOpenEmbedding hM hinf hpair hunion hpower hsep a)ᶜ := by
  let _ := Alg
  change cohenRegularCompletionIso (decodeInternalRegular cohenOrderGraph_correct M aᶜ) = _
  rw [decodeInternalRegular_compl hM hinf hpair hunion hsep P R cohenOrderGraph_correct, map_compl]
  rfl


end PolishSpaceBook
