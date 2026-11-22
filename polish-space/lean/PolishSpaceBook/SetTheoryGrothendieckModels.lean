module

public import PolishSpaceBook.SetTheoryInaccessibleUniverse
public import PolishSpaceBook.SetTheoryChoice
public import PolishSpaceBook.ForcingOrdinalPreservation

@[expose] public section

/-! # Grothendieck closure implies satisfaction of the membership-language axioms -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u
namespace IsGrothendieckUniverse
variable {U : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
include hU

/-- Indexed unions of singletons collect the image of any externally given set-indexed map. -/
lemma range_mem {x : ZFSet.{u}} (hx : x ∈ U) (f : x → ZFSet.{u})
    (hf : ∀ a, f a ∈ U) : ZFSet.range f ∈ U := by
  have h := hU.indexedUnion_mem hx (fun a => ({f a} : ZFSet.{u}))
    (fun a => hU.singleton_mem (hf a))
  have he : ZFSet.iUnion (fun a => ({f a} : ZFSet.{u})) = ZFSet.range f := by
    ext z
    simp only [ZFSet.mem_iUnion, ZFSet.mem_singleton, ZFSet.mem_range, eq_comm]
  exact he ▸ h

lemma models_pairing : U ⊨ pairingSentence := by
  apply (models_pairing_iff U).mpr
  intro a b
  refine ⟨⟨{a.val, b.val}, hU.pair_mem a.property b.property⟩, ?_⟩
  intro z
  simp only [ZFSet.mem_pair, Subtype.ext_iff]

lemma models_union : U ⊨ unionSentence := by
  apply (models_union_iff U).mpr
  intro x
  refine ⟨⟨ZFSet.sUnion x.val, hU.sUnion_mem x.property⟩, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := ZFSet.mem_sUnion.mp hz
    exact ⟨⟨y, hU.transitive.mem_trans hy x.property⟩, hzy, hy⟩
  · rintro ⟨y, hzy, hy⟩
    exact ZFSet.mem_sUnion.mpr ⟨y.val, hy, hzy⟩

lemma models_power : U ⊨ powerSentence := by
  apply (models_power_iff U).mpr
  intro x
  refine ⟨⟨ZFSet.powerset x.val, hU.powerset_mem x.property⟩, ?_⟩
  intro z
  exact ZFSet.mem_powerset.trans (subset_iff_internal hU.transitive z.property)

lemma models_infinity : U ⊨ infinitySentence :=
  models_infinity_of_omegaOrdinal_mem hU.transitive hU.omega_mem

/-- The quantified outputs are elements of U; no absoluteness assumption on the formula is used. -/
lemma models_replacement {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    U ⊨ replacementSentence φ := by
  classical
  apply (realize_replacement U φ).mpr
  intro ps x hx
  let input (a : x.val) : U := ⟨a.val, hU.transitive.mem_trans a.property x.property⟩
  have hex (a : x.val) : ∃! b : U,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps (input a)) b) := hx (input a) a.property
  let f (a : x.val) : U := (hex a).exists.choose
  have hf (a : x.val) : φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps (input a)) (f a)) :=
    (hex a).exists.choose_spec
  refine ⟨⟨ZFSet.range (fun a => (f a).val),
    hU.range_mem x.property _ (fun a => (f a).property)⟩, ?_⟩
  intro b
  constructor
  · intro hb
    obtain ⟨a, hab⟩ := ZFSet.mem_range.mp hb
    have he : f a = b := Subtype.ext hab
    exact ⟨input a, a.property, he ▸ hf a⟩
  · rintro ⟨a, ha, hab⟩
    let i : x.val := ⟨a.val, ha⟩
    have hi : input i = a := rfl
    apply ZFSet.mem_range.mpr
    refine ⟨i, congrArg Subtype.val ((hex i).unique (hf i) ?_)⟩
    simpa only [hi] using hab

lemma models_separation {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    U ⊨ separationSentence φ :=
  models_separation_of_replacement U (models_extensionality hU.transitive)
    hU.models_infinity hU.models_pairing hU.models_union φ (hU.models_replacement _)

/-- External choice selects values; universe closure puts the entire choice graph inside U. -/
lemma models_choice : U ⊨ choiceSentence := by
  classical
  apply (models_choice_iff hU.transitive hU.models_union).mpr
  intro A hA
  have hex (a : A.val) : ∃ b : ZFSet.{u}, b ∈ a.val := hA a.val a.property
  let f (a : A.val) : ZFSet.{u} := (hex a).choose
  have hf (a : A.val) : f a ∈ a.val := (hex a).choose_spec
  have hgraph : functionGraph f ∈ U := by
    apply hU.range_mem A.property
    intro a
    have ha := hU.transitive.mem_trans a.property A.property
    have hb := hU.transitive.mem_trans (hf a) ha
    exact hU.pair_mem (hU.singleton_mem ha) (hU.pair_mem ha hb)
  refine ⟨⟨functionGraph f, hgraph⟩, ⟨?_, (functionGraph_isFunc f).2⟩, ?_⟩
  · intro z hz
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨a.property,
      ZFSet.mem_sUnion.mpr ⟨a.val, a.property, hf a⟩⟩
  · intro a ha
    exact ⟨f ⟨a, ha⟩, hf ⟨a, ha⟩, ZFSet.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩⟩

end IsGrothendieckUniverse
/-- Exactly the eight axiom families displayed in the book; Replacement ranges over all formulas. -/
inductive ZFCAxiom : membershipLanguage.Sentence → Prop
  | extensionality : ZFCAxiom extensionalitySentence
  | pairing : ZFCAxiom pairingSentence
  | union : ZFCAxiom unionSentence
  | power : ZFCAxiom powerSentence
  | infinity : ZFCAxiom infinitySentence
  | foundation : ZFCAxiom foundationSentence
  | choice : ZFCAxiom choiceSentence
  | replacement {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ZFCAxiom (replacementSentence φ)

/-- The full membership-language theory, rather than a chosen finite fragment. -/
def fullZFCTheory : membershipLanguage.Theory := {φ | ZFCAxiom φ}

/-- Universe closure proves every axiom and every Replacement instance of the actual theory. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    An inaccessible cardinal $\kappa$ is a stronger sufficient closure hypothesis ensuring
    that $V_\kappa$ is a
    transitive model of full ZFC.
-/
theorem IsGrothendieckUniverse.models_fullZFC {U : ZFSet.{u}}
    (hU : IsGrothendieckUniverse U) : U ⊨ fullZFCTheory := by
  constructor
  intro φ hφ
  cases hφ with
  | extensionality => exact models_extensionality hU.transitive
  | pairing => exact hU.models_pairing
  | union => exact hU.models_union
  | power => exact hU.models_power
  | infinity => exact hU.models_infinity
  | foundation => exact models_foundation hU.transitive
  | choice => exact hU.models_choice
  | replacement φ => exact hU.models_replacement φ

/-- An inaccessible stage is a transitive model of all of ZFC simultaneously. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    An inaccessible cardinal $\kappa$ is a stronger sufficient closure hypothesis ensuring
    that $V_\kappa$ is a
    transitive model of full ZFC.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $\kappa$ is inaccessible, then $V_\kappa$ is a transitive
    model of full ZFC by §{sec:inaccessible-universes}.
-/
theorem inaccessible_stage_models_fullZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    (ZFSet.vonNeumann κ.ord).IsTransitive ∧ ZFSet.vonNeumann κ.ord ⊨ fullZFCTheory := by
  have hU := inaccessible_vonNeumann_isGrothendieckUniverse hκ
  exact ⟨hU.transitive, hU.models_fullZFC⟩

end PolishSpaceBook.SetTheoryModels
