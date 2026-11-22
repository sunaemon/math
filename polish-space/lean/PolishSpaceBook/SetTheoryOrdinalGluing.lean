module

public import PolishSpaceBook.SetTheoryOrdinalInitialSegments

@[expose] public section

/-! # Assembling ordinal representations of predecessor segments

Only a strict total order is assumed. The representations of its predecessor
segments supply the compatibility needed to construct the representation of
the whole order; external well-foundedness is not an additional hypothesis.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma orderPredecessors_nested {A R : ZFSet.{u}}
    [IsTrans A (fun x y : A => pair x.val y.val ∈ R)] {a b : A}
    (hab : pair a.val b.val ∈ R) :
    orderPredecessors (orderPredecessors A R b.val) R a.val = orderPredecessors A R a.val := by
  apply ZFSet.ext
  intro x
  simp only [mem_orderPredecessors]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, trans_of (fun x y : A => pair x.val y.val ∈ R)
      (a := ⟨x, h.1⟩) h.2 hab⟩, h.2⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Write $aRb$ for $\langle a,b\rangle\in R$.
    Let $\beta_a$ be the unique ordinal selected by $\psi$, and let $f_a:D_a\to\beta_a$ be its representation.
    If $aRb$, transitivity of the order gives
    $$\{x\in D_b:xRa\}=D_a.$$
    Restricting the actual order-isomorphism $f_b$ to this segment gives a representation of $D_a$ onto $f_b(a)$.
    Uniqueness of ordinal representations gives
    $$\beta_a=f_b(a)\in\beta_b.$$
    Consequently $a\mapsto\beta_a$ is injective: for distinct points, linearity makes one image belong to the other,
    so equal images would contradict Foundation.
    The same comparison and asymmetry of membership show
    $$\beta_a\in\beta_b\quad\Longleftrightarrow\quad aRb.$$
-/
theorem ordinalInitial_target {A R : ZFSet.{u}}
    [IsTrans A (fun x y : A => pair x.val y.val ∈ R)]
    (α : A → ZFSet.{u}) (hα : ∀ a, (α a).IsOrdinal)
    (e : ∀ a : A, (fun x y : orderPredecessors A R a.val => pair x.val y.val ∈ R) ≃r
      (fun b c : α a => b.val ∈ c.val))
    {a b : A} (hab : pair a.val b.val ∈ R) :
    α a = (e b ⟨a.val, mem_orderPredecessors.mpr ⟨a.property, hab⟩⟩).val := by
  let a' : orderPredecessors A R b.val := ⟨a.val, mem_orderPredecessors.mpr ⟨a.property, hab⟩⟩
  have er := ordinalIsoInitial (hα b) (e b) a'
  change (fun x y : orderPredecessors (orderPredecessors A R b.val) R a.val => pair x.val y.val ∈ R) ≃r
    (fun c d : (e b a').val => c.val ∈ d.val) at er
  rw [orderPredecessors_nested hab] at er
  exact ordinal_eq_of_relIso (hα a) ((hα b).mem (e b a').property) ((e a).symm.trans er)

variable {A R : ZFSet.{u}} [IsStrictTotalOrder A (fun x y : A => pair x.val y.val ∈ R)]
variable (α : A → ZFSet.{u}) (hα : ∀ a, (α a).IsOrdinal)
variable (e : ∀ a : A, (fun x y : orderPredecessors A R a.val => pair x.val y.val ∈ R) ≃r
  (fun b c : α a => b.val ∈ c.val))

include hα e

lemma ordinalInitial_mem_of_rel {a b : A} (hab : pair a.val b.val ∈ R) : α a ∈ α b := by
  rw [ordinalInitial_target α hα e hab]
  exact (e b _).property

theorem ordinalInitial_injective : Function.Injective α := by
  intro a b he
  rcases trichotomous_of (fun x y : A => pair x.val y.val ∈ R) a b with hab | heq | hba
  · exact False.elim (ZFSet.mem_irrefl _ (he ▸ ordinalInitial_mem_of_rel α hα e hab))
  · exact heq
  · exact False.elim (ZFSet.mem_irrefl _ (he.symm ▸ ordinalInitial_mem_of_rel α hα e hba))

theorem ordinalInitial_mem_iff (a b : A) : α a ∈ α b ↔ pair a.val b.val ∈ R := by
  refine ⟨?_, ordinalInitial_mem_of_rel α hα e⟩
  intro h
  rcases trichotomous_of (fun x y : A => pair x.val y.val ∈ R) a b with hab | heq | hba
  · exact hab
  · exact False.elim (ZFSet.mem_irrefl _ (heq ▸ h))
  · exact False.elim (ZFSet.mem_asymm h (ordinalInitial_mem_of_rel α hα e hba))

theorem ordinalInitial_range_isOrdinal : (ZFSet.range α).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  refine ⟨?_, ?_⟩
  · intro z hz b hb
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    let y := (e a).symm ⟨b, hb⟩
    let yA : A := ⟨y.val, (mem_orderPredecessors.mp y.property).1⟩
    have hy : pair yA.val a.val ∈ R := (mem_orderPredecessors.mp y.property).2
    apply ZFSet.mem_range.mpr
    refine ⟨yA, ?_⟩
    rw [ordinalInitial_target α hα e hy]
    exact congrArg (fun z : α a => z.val) ((e a).apply_symm_apply ⟨b, hb⟩)
  · intro z hz
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    exact hα a

def ordinalGluingIso :
    (fun x y : A => pair x.val y.val ∈ R) ≃r (fun b c : ZFSet.range α => b.val ∈ c.val) := by
  let g : A → ZFSet.range α := fun a => ⟨α a, ZFSet.mem_range.mpr ⟨a, rfl⟩⟩
  have hi : Function.Injective g := fun a b h =>
    ordinalInitial_injective α hα e (congrArg (fun z : ZFSet.range α => z.val) h)
  have hs : Function.Surjective g := by
    intro b
    obtain ⟨a, ha⟩ := ZFSet.mem_range.mp b.property
    exact ⟨a, Subtype.ext ha⟩
  exact { Equiv.ofBijective g ⟨hi, hs⟩ with map_rel_iff' := ordinalInitial_mem_iff α hα e _ _ }

end PolishSpaceBook.SetTheoryModels
