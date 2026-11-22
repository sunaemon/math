module

public import PolishSpaceBook.MeasureAlgebra
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

/-!
# Measure-preserving maps inverse off null sets

Restrict mutually inverse almost-everywhere maps to conull Borel subspaces,
and descend their inverse-image maps to the measure algebras.
-/

noncomputable section
namespace PolishSpaceBook
open Set Filter Function MeasureTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}

/-- Internal data for maps which become inverse after discarding null sets. -/
structure AEMeasureEquiv (μ : Measure X) (ν : Measure Y) where
  forward : X → Y
  backward : Y → X
  forward_preserving : MeasurePreserving forward μ ν
  backward_preserving : MeasurePreserving backward ν μ
  left_inv : ∀ᵐ x ∂μ, backward (forward x) = x
  right_inv : ∀ᵐ y ∂ν, forward (backward y) = y

namespace AEMeasureEquiv

def symm (e : AEMeasureEquiv μ ν) : AEMeasureEquiv ν μ where
  forward := e.backward
  backward := e.forward
  forward_preserving := e.backward_preserving
  backward_preserving := e.forward_preserving
  left_inv := e.right_inv
  right_inv := e.left_inv

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Construct $f_Y,g_Y$ in the same way for $(Y,\nu)$, and set
    $$h:=g_Y\circ f_X:X\to Y,\qquad k:=g_X\circ f_Y:Y\to X.$$
    These Borel maps preserve measure. They satisfy $k(h(x))=x$ for $\mu$-almost every $x$ and
    $h(k(y))=y$ for $\nu$-almost every $y$. For example, the first identity follows from
    $$k(h(x))=g_X(f_Y(g_Y(f_X(x))))=g_X(f_X(x))=x.$$
    The middle equality fails only when $f_X(x)$ belongs to a $\lambda$-null exceptional set, whose inverse image
    is $\mu$-null because $(f_X)_*\mu=\lambda$. The other identity follows in the same way.
-/
/-- Composition transports each exceptional set through a measure-preserving map. -/
def trans (e : AEMeasureEquiv μ ν) (d : AEMeasureEquiv ν ρ) : AEMeasureEquiv μ ρ where
  forward := d.forward ∘ e.forward
  backward := e.backward ∘ d.backward
  forward_preserving := d.forward_preserving.comp e.forward_preserving
  backward_preserving := e.backward_preserving.comp d.backward_preserving
  left_inv := by
    filter_upwards [e.left_inv, e.forward_preserving.quasiMeasurePreserving.ae d.left_inv] with x hx hd
    change e.backward (d.backward (d.forward (e.forward x))) = x
    rw [hd, hx]
  right_inv := by
    filter_upwards [d.right_inv, d.backward_preserving.quasiMeasurePreserving.ae e.right_inv] with z hz he
    change d.forward (e.forward (e.backward (d.backward z))) = z
    rw [he, hz]

variable (e : AEMeasureEquiv μ ν)

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    To obtain exact inverse maps on Borel subspaces, put
    $$\begin{aligned}
    L&:=\{x:k(h(x))=x\},&R&:=\{y:h(k(y))=y\},\\
    X_0&:=L\cap h^{-1}(R),&Y_0&:=R.
    \end{aligned}$$
    Both $L$ and $R$ are conull Borel sets, and $h$ preserves measure, so $X_0$ and $Y_0$ are conull Borel sets.
    For $x\in X_0$ we have $h(x)\in Y_0$ and $k(h(x))=x$. If $y\in Y_0$, then $h(k(y))=y$ and
    $k(h(k(y)))=k(y)$, so $k(y)\in X_0$. Hence the restrictions of $h$ and $k$ are inverse Borel maps
    between $X_0$ and $Y_0$. Restricting the pushforward identities shows that they preserve the subspace measures.
-/
/-- Keep both inverse identities on the source so the restricted maps have exact inverses. -/
def source : Set X := {x | e.backward (e.forward x) = x} ∩
  e.forward ⁻¹' {y | e.forward (e.backward y) = y}

def target : Set Y := {y | e.forward (e.backward y) = y}

lemma ae_source : ∀ᵐ x ∂μ, x ∈ e.source := by
  filter_upwards [e.left_inv, e.forward_preserving.quasiMeasurePreserving.ae e.right_inv] with x hx hy
  exact ⟨hx, hy⟩

lemma ae_target : ∀ᵐ y ∂ν, y ∈ e.target := e.right_inv

lemma backward_mem_source {y : Y} (hy : y ∈ e.target) : e.backward y ∈ e.source := by
  exact ⟨congrArg e.backward hy, congrArg (e.forward ∘ e.backward) hy⟩

variable [MeasurableEq X] [MeasurableEq Y]

lemma measurable_source : MeasurableSet e.source :=
  (measurableSet_eq_fun (e.backward_preserving.measurable.comp e.forward_preserving.measurable)
    measurable_id).inter (e.forward_preserving.measurable
      (measurableSet_eq_fun (e.forward_preserving.measurable.comp e.backward_preserving.measurable)
        measurable_id))

omit [MeasurableEq X] in
lemma measurable_target : MeasurableSet e.target :=
  measurableSet_eq_fun (e.forward_preserving.measurable.comp e.backward_preserving.measurable) measurable_id

/-- Exact Borel isomorphism on the chosen conull subspaces. -/
def conullEquiv (e : AEMeasureEquiv μ ν) : e.source ≃ᵐ e.target where
  toFun x := ⟨e.forward x, x.2.2⟩
  invFun y := ⟨e.backward y, e.backward_mem_source y.2⟩
  left_inv x := Subtype.ext x.2.1
  right_inv y := Subtype.ext y.2
  measurable_toFun := (e.forward_preserving.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.backward_preserving.measurable.comp measurable_subtype_coe).subtype_mk

lemma conullEquiv_preserving : MeasurePreserving e.conullEquiv
    (μ.comap Subtype.val) (ν.comap Subtype.val) := by
  refine ⟨e.conullEquiv.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe e.measurable_target).map_injective
  rw [Measure.map_map measurable_subtype_coe e.conullEquiv.measurable,
    map_comap_subtype_coe e.measurable_target, Measure.restrict_eq_self_of_ae_mem e.ae_target]
  change (μ.comap Subtype.val).map (e.forward ∘ Subtype.val) = ν
  rw [← Measure.map_map e.forward_preserving.measurable measurable_subtype_coe,
    map_comap_subtype_coe e.measurable_source, Measure.restrict_eq_self_of_ae_mem e.ae_source]
  exact e.forward_preserving.map_eq

/-- Canonical measurable-space formulation, with the two discarded sets explicitly null. -/
theorem exists_conull_isomorphism (e : AEMeasureEquiv μ ν) : ∃ (A : Set X) (B : Set Y),
    MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
    ∃ f : A ≃ᵐ B, MeasurePreserving f (μ.comap Subtype.val) (ν.comap Subtype.val) :=
  ⟨e.source, e.target, e.measurable_source, e.measurable_target,
    ae_iff.mp e.ae_source, ae_iff.mp e.ae_target, e.conullEquiv, e.conullEquiv_preserving⟩

end AEMeasureEquiv

namespace MeasureAlgebra

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Inverse images under $h$ and $k$ preserve null sets, so these maps are well-defined.
-/
/-- Inverse image descends to null-equivalence classes under a measure-preserving map. -/
def pullback {f : X → Y} (hf : MeasurePreserving f μ ν) : MeasureAlgebra ν → MeasureAlgebra μ :=
  Quotient.lift (fun A => mk (f ⁻¹' (A : Set Y)) (hf.measurable A.property)) (by
    intro A B h
    exact Quotient.sound (hf.quasiMeasurePreserving.preimage_ae_eq h))

lemma pullback_monotone {f : X → Y} (hf : MeasurePreserving f μ ν) : Monotone (pullback hf) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B => exact hf.quasiMeasurePreserving.preimage_mono_ae

lemma pullback_mass {f : X → Y} (hf : MeasurePreserving f μ ν) (a : MeasureAlgebra ν) :
    mass (pullback hf a) = mass a := by
  induction a using Quotient.inductionOn with
  | h A => exact hf.measure_preimage A.property.nullMeasurableSet

lemma pullback_inverse (e : AEMeasureEquiv μ ν) (a : MeasureAlgebra μ) :
    pullback e.forward_preserving (pullback e.backward_preserving a) = a := by
  induction a using Quotient.inductionOn with
  | h A =>
    apply Quotient.sound
    filter_upwards [e.left_inv] with x hx
    change (e.backward (e.forward x) ∈ (A : Set X)) = (x ∈ (A : Set X))
    rw [hx]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    They preserve Boolean operations
    because inverse images do. The almost-everywhere inverse identities imply that $\Phi$ and $\Psi$ are inverse.
-/
/-- The two inverse-image maps give an order isomorphism, hence a Boolean algebra isomorphism. -/
def ofAEEquiv (e : AEMeasureEquiv μ ν) : MeasureAlgebra μ ≃o MeasureAlgebra ν where
  toFun := pullback e.backward_preserving
  invFun := pullback e.forward_preserving
  left_inv := pullback_inverse e
  right_inv := pullback_inverse e.symm
  map_rel_iff' := by
    intro a b
    change pullback e.backward_preserving a ≤ pullback e.backward_preserving b ↔ a ≤ b
    constructor
    · intro h
      have H := pullback_monotone e.forward_preserving h
      simpa only [pullback_inverse] using H
    · exact fun h => pullback_monotone e.backward_preserving h

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Finally,
    $$\nu(k^{-1}(S))=\mu(S),\qquad \mu(h^{-1}(T))=\nu(T),$$
    so the isomorphisms preserve measure.
-/
/-- The inverse-image formula preserves the mass of each quotient class. -/
lemma ofAEEquiv_mass (e : AEMeasureEquiv μ ν) (a : MeasureAlgebra μ) :
    mass (ofAEEquiv e a) = mass a := pullback_mass e.backward_preserving a

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For a Borel set $S\IncludedIn X$, the sets $h(S\cap X_0)$ and $k^{-1}(S)$ agree on $Y_0$.
    The first is Borel because the restriction of $h$ is a Borel isomorphism.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Thus the induced maps on measure algebras are
-/
/-- On the conull target, the inverse image under the backward map is exactly
 the image of the original set under the restricted forward Borel isomorphism. -/
lemma backward_preimage_ae_image [MeasurableEq X] [MeasurableEq Y]
    (e : AEMeasureEquiv μ ν) (S : Set X) :
    e.backward ⁻¹' S =ᵐ[ν]
      Subtype.val '' (e.conullEquiv '' (Subtype.val ⁻¹' S : Set e.source)) := by
  filter_upwards [e.ae_target] with y hy
  apply propext
  constructor
  · intro h
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    refine ⟨⟨e.backward y, e.backward_mem_source hy⟩, h, ?_⟩
    exact Subtype.ext hy
  · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
    change e.backward y ∈ S
    rw [← hz]
    change e.backward (e.forward x) ∈ S
    rwa [x.2.1]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    $$\begin{aligned}
    \Phi([S])&:=[h(S\cap X_0)]=[k^{-1}(S)],\\
    \Psi([T])&:=[h^{-1}(T)].
    \end{aligned}$$
-/
/-- The quotient isomorphism has the forward-image formula used in the book. -/
lemma ofAEEquiv_mk_image [MeasurableEq X] [MeasurableEq Y]
    (e : AEMeasureEquiv μ ν) (S : Set X) (hS : MeasurableSet S) :
    ofAEEquiv e (mk S hS) =
      mk (Subtype.val '' (e.conullEquiv '' (Subtype.val ⁻¹' S : Set e.source)))
        ((MeasurableEmbedding.subtype_coe e.measurable_target).measurableSet_image'
          (e.conullEquiv.measurableEmbedding.measurableSet_image' (measurable_subtype_coe hS))) :=
  Quotient.sound (backward_preimage_ae_image e S)

end MeasureAlgebra
end PolishSpaceBook
