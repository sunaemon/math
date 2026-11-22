module

public import PolishSpaceBook.RepresentedContinuousMaps
public import PolishSpaceBook.RepresentedProducts
public import PolishSpaceBook.RepresentedCoproducts

@[expose] public section

/-! # Continuous operations on names and represented products -/
namespace PolishSpaceBook
open Function
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Pointwise pairing is continuous for arbitrary continuously varying names. -/
theorem continuous_typeTwoPairName {A : Type*} [TopologicalSpace A]
    {P Q : A → (ℕ → ℕ)} (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (fun a => typeTwoPairName (P a) (Q a)) := by
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology (f := fun z : ℕ × ℕ => Nat.pair z.1 z.2)).comp
    (((continuous_apply i).comp hP).prodMk ((continuous_apply i).comp hQ))

theorem continuous_typeTwoLeftName : Continuous typeTwoLeftName := by
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology (f := fun n : ℕ => n.unpair.1)).comp (continuous_apply i)

theorem continuous_typeTwoRightName : Continuous typeTwoRightName := by
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology (f := fun n : ℕ => n.unpair.2)).comp (continuous_apply i)

theorem continuous_typeTwoTagName (e : ℕ) : Continuous (typeTwoTagName e) := by
  apply continuous_pi
  intro i
  cases i with
  | zero => exact continuous_const
  | succ i => exact continuous_apply i

theorem HasContinuousRealizer.comp {δX : Representation X} {δY : Representation Y}
    {δZ : Representation Z} {f : X → Y} {g : Y → Z}
    (hg : HasContinuousRealizer δY δZ g) (hf : HasContinuousRealizer δX δY f) :
    HasContinuousRealizer δX δZ (g ∘ f) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  exact ⟨G ∘ F, hG.comp (hF.subtype_mk _), hg.comp hf⟩

theorem continuous_realizer_product_iff (δZ : Representation Z) (δX : Representation X)
    (δY : Representation Y) (h : Z → X × Y) :
    HasContinuousRealizer δZ (typeTwoProductRepresentation δX δY) h ↔
      HasContinuousRealizer δZ δX (Prod.fst ∘ h) ∧
      HasContinuousRealizer δZ δY (Prod.snd ∘ h) := by
  constructor
  · rintro ⟨H, hH, hr⟩
    constructor
    · refine ⟨fun p => ⟨typeTwoLeftName (H p).val, (H p).property.1⟩,
        continuous_typeTwoLeftName.comp hH, ?_⟩
      intro p
      exact congrArg Prod.fst (hr p)
    · refine ⟨fun p => ⟨typeTwoRightName (H p).val, (H p).property.2⟩,
        continuous_typeTwoRightName.comp hH, ?_⟩
      intro p
      exact congrArg Prod.snd (hr p)
  · rintro ⟨⟨F, hF, hf⟩, ⟨G, hG, hg⟩⟩
    let H : δZ.domain → (typeTwoProductRepresentation δX δY).domain := fun p =>
      ⟨typeTwoPairName (F p).val (G p).val, by simp [typeTwoProductRepresentation]⟩
    refine ⟨H, continuous_typeTwoPairName hF hG, ?_⟩
    intro p
    change (δX.toFun _, δY.toFun _) = h (δZ.toFun p)
    simpa [H] using Prod.ext (hf p) (hg p)

end PolishSpaceBook
