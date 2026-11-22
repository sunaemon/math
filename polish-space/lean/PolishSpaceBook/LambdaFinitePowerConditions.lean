module

public import PolishSpaceBook.LambdaAnalyticCatalog
public import PolishSpaceBook.LambdaProjectionOperations
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm MeasureTheory
namespace LambdaTree

/-- Dimension is `n+1`, so the last coordinate is retained rather than padded. -/
def packPowerDigits : (n : ℕ) → (Fin (n+1) → ℕ) → ℕ
  | 0, v => v 0
  | n+1, v => Nat.pair (v 0) (packPowerDigits n (fun i => v i.succ))

def unpackPowerDigits : (n : ℕ) → ℕ → Fin (n+1) → ℕ
  | 0, z, _ => z
  | n+1, z, i => Fin.cases z.unpair.1 (fun j => unpackPowerDigits n z.unpair.2 j) i

@[simp] theorem unpack_packPowerDigits (n : ℕ) (v : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    unpackPowerDigits n (packPowerDigits n v) i = v i := by
  induction n with
  | zero => have hi : i = 0 := Fin.ext (by have := i.isLt; omega); subst i; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [packPowerDigits, unpackPowerDigits]
    · simpa [packPowerDigits, unpackPowerDigits] using ih (fun j => v j.succ) j

@[simp] theorem pack_unpackPowerDigits (n z : ℕ) :
    packPowerDigits n (unpackPowerDigits n z) = z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [packPowerDigits, unpackPowerDigits, ih, Nat.pair_unpair]

def encodePower (n : ℕ) (x : Fin (n+1) → (ℕ → ℕ)) (k : ℕ) : ℕ :=
  packPowerDigits n (fun i => x i k)
def decodePower (n : ℕ) (p : ℕ → ℕ) (i : Fin (n+1)) (k : ℕ) : ℕ :=
  unpackPowerDigits n (p k) i

@[simp] theorem decode_encodePower (n : ℕ) (x : Fin (n+1) → (ℕ → ℕ)) :
    decodePower n (encodePower n x) = x := by
  funext i k
  exact unpack_packPowerDigits n (fun i => x i k) i

@[simp] theorem encode_decodePower (n : ℕ) (p : ℕ → ℕ) :
    encodePower n (decodePower n p) = p := by
  funext k
  exact pack_unpackPowerDigits n (p k)

def finitePowerEquiv (n : ℕ) : (Fin (n+1) → (ℕ → ℕ)) ≃ (ℕ → ℕ) where
  toFun := encodePower n
  invFun := decodePower n
  left_inv := decode_encodePower n
  right_inv := encode_decodePower n

theorem encodePower_injective (n : ℕ) : Function.Injective (encodePower n) :=
  (finitePowerEquiv n).injective

theorem continuous_encodePower (n : ℕ) : Continuous (encodePower n) := by
  apply continuous_pi
  intro k
  exact (continuous_of_discreteTopology (f := packPowerDigits n)).comp
    (continuous_pi (fun i => (continuous_apply k).comp (continuous_apply i)))

theorem continuous_decodePower (n : ℕ) : Continuous (decodePower n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact (continuous_of_discreteTopology (f := fun z => unpackPowerDigits n z i)).comp
    (continuous_apply k)

def finitePowerHomeomorph (n : ℕ) : (Fin (n+1) → (ℕ → ℕ)) ≃ₜ (ℕ → ℕ) where
  toEquiv := finitePowerEquiv n
  continuous_toFun := continuous_encodePower n
  continuous_invFun := continuous_decodePower n

/-- Each fixed coordinate is read by a finite composition of numerical projections. -/
def powerProjectionProgram : (n : ℕ) → Fin (n+1) → AlphaTerm
  | 0, _ => numericalIdentity
  | n+1, i => Fin.cases (numericalProjectionTerm true)
      (fun j => numericalCompose (powerProjectionProgram n j) (numericalProjectionTerm false)) i

theorem powerProjectionProgram_computes (n : ℕ) (i : Fin (n+1)) :
    NumericalComputes (powerProjectionProgram n i) (fun z => unpackPowerDigits n z i) := by
  induction n with
  | zero => exact numericalIdentity_computes
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact projection_computes true
    · exact (ih j).comp (projection_computes false)

def powerPackProgram : (n : ℕ) → (Fin (n+1) → AlphaTerm) → AlphaTerm
  | 0, P => P 0
  | n+1, P => pairNumerical (P 0) (powerPackProgram n (fun i => P i.succ))

theorem powerPackProgram_computes (n : ℕ) (P : Fin (n+1) → AlphaTerm)
    (f : Fin (n+1) → ℕ → ℕ) (hP : ∀ i, NumericalComputes (P i) (f i)) :
    NumericalComputes (powerPackProgram n P) (fun z => packPowerDigits n (fun i => f i z)) := by
  induction n with
  | zero => exact hP 0
  | succ n ih => exact (hP 0).pair (ih (fun i => P i.succ) (fun i => f i.succ) (fun i => hP i.succ))

/-- Relative analyticity on a positive finite power uses its explicit recursive code. -/
def PowerProjected (ε : ℕ → ℕ) (n : ℕ) (A : Set (Fin (n+1) → (ℕ → ℕ))) : Prop :=
  Projected ε (encodePower n '' A)

theorem countable_powerProjected (ε : ℕ → ℕ) (n : ℕ) :
    {A | PowerProjected ε n A}.Countable :=
  (countable_projected ε).preimage (Set.image_injective.mpr (encodePower_injective n))

/-- Conditions are sets, so distinct indices denoting the same set are identified. -/
abbrev PowerCondition (ε : ℕ → ℕ) (n : ℕ) :=
  {A : Set (Fin (n+1) → (ℕ → ℕ)) // A.Nonempty ∧ PowerProjected ε n A}

instance powerCondition_countable (ε : ℕ → ℕ) (n : ℕ) : Countable (PowerCondition ε n) :=
  ((countable_powerProjected ε n).mono (fun _ h => h.2)).to_subtype

theorem powerCondition_le_iff (ε : ℕ → ℕ) (n : ℕ) (P Q : PowerCondition ε n) :
    P ≤ Q ↔ P.val ⊆ Q.val := Iff.rfl

theorem PowerProjected.inter {ε : ℕ → ℕ} {n : ℕ}
    {A B : Set (Fin (n+1) → (ℕ → ℕ))} (hA : PowerProjected ε n A) (hB : PowerProjected ε n B) :
    PowerProjected ε n (A ∩ B) := by
  unfold PowerProjected
  rw [Set.image_inter (encodePower_injective n)]
  exact Projected.inter hA hB

/-- Coordinate cylinders retain the fixed parameter via the projection programs. -/
theorem PowerProjected.coordinateCylinder (ε : ℕ → ℕ) (n : ℕ) (i : Fin (n+1)) (s : List ℕ) :
    PowerProjected ε n {x | x i ∈ cyl s} := by
  have h := (projected_cyl ε s).coordinatePreimage
    (powerProjectionProgram_computes n i)
  have he : encodePower n '' {x | x i ∈ cyl s} =
      {p | (fun k => unpackPowerDigits n (p k) i) ∈ cyl s} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (fun k => unpackPowerDigits n (encodePower n x k) i) ∈ cyl s
      change x i ∈ cyl s at hx
      simpa only [encodePower, unpack_packPowerDigits] using hx
    · intro hp
      exact ⟨decodePower n p, hp, encode_decodePower n p⟩
  rw [PowerProjected, he]
  change Projected ε ((fun p => (fun z => unpackPowerDigits n z i) ∘ p) ⁻¹' cyl s)
  exact h

/-- A finite family of ordinary coordinate cylinders is again relative analytic. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    This supplies precisely the refinements used in the next proof. Closure under arbitrary analytic
    subsets of a condition is not required: those subsets might fail to have a presentation at the fixed
    parameter. For finite powers of Baire space, repeat the coordinate-pairing construction of
    §{sec:edst-coordinate-projections} to apply the same argument.
-/
theorem PowerProjected.productCylinder (ε : ℕ → ℕ) (n : ℕ)
    (s : Fin (n+1) → List ℕ) : PowerProjected ε n {x | ∀ i, x i ∈ cyl (s i)} := by
  have hu : PowerProjected ε n Set.univ := by
    unfold PowerProjected
    rw [Set.image_univ, (show Function.Surjective (encodePower n) from fun p => ⟨decodePower n p, encode_decodePower n p⟩).range_eq]
    simpa [cyl] using projected_cyl ε []
  have hf (S : Finset (Fin (n+1))) : PowerProjected ε n {x | ∀ i ∈ S, x i ∈ cyl (s i)} := by
    induction S using Finset.induction_on with
    | empty => simpa using hu
    | @insert j S hj ih =>
      convert (PowerProjected.coordinateCylinder ε n j (s j)).inter ih using 1
      ext x
      simp only [mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, mem_inter_iff]
  simpa only [Finset.mem_univ, forall_const] using hf Finset.univ

/-- Closed witness presentations are pulled back through the constructed homeomorphism. -/
def powerClosedPresentation (ε : ℕ → ℕ) (n e : ℕ) :
    Set ((Fin (n+1) → (ℕ → ℕ)) × (ℕ → ℕ)) :=
  {z | (encodePower n z.1, z.2) ∈ pairTreeBody (indexedTree ε e).tree}

theorem powerClosedPresentation_closed (ε : ℕ → ℕ) (n e : ℕ) :
    IsClosed (powerClosedPresentation ε n e) :=
  (isClosed_pairTreeBody _).preimage
    (((continuous_encodePower n).comp continuous_fst).prodMk continuous_snd)

theorem powerCondition_closed_presentation (ε : ℕ → ℕ) (n : ℕ) (P : PowerCondition ε n) :
    ∃ e, P.val = Prod.fst '' powerClosedPresentation ε n e := by
  obtain ⟨e, he⟩ := (projected_iff_index ε (encodePower n '' P.val)).mp P.property.2
  refine ⟨e, ?_⟩
  ext x
  constructor
  · intro hx
    have hc : encodePower n x ∈ indexedProjection ε e := he ▸ ⟨x, hx, rfl⟩
    obtain ⟨q, hq⟩ := hc
    exact ⟨(x,q), hq, rfl⟩
  · rintro ⟨⟨y,q⟩, hq, rfl⟩
    have hc : encodePower n y ∈ indexedProjection ε e := ⟨q, hq⟩
    rw [← he] at hc
    obtain ⟨z, hz, hzy⟩ := hc
    exact (encodePower_injective n hzy) ▸ hz

/-- Witness restrictions and point-cylinder refinements retain the same parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    This supplies precisely the refinements used in the next proof. Closure under arbitrary analytic
    subsets of a condition is not required: those subsets might fail to have a presentation at the fixed
    parameter. For finite powers of Baire space, repeat the coordinate-pairing construction of
    §{sec:edst-coordinate-projections} to apply the same argument.
-/
theorem PowerProjected.witnessCell (ε : ℕ → ℕ) (n e k : ℕ)
    (s t : FusionPrefix k) :
    PowerProjected ε n {x | encodePower n x ∈
      witnessProjection (pairTreeBody (indexedTree ε e).tree) s t} := by
  unfold PowerProjected
  change Projected ε (encodePower n '' ((encodePower n) ⁻¹'
    witnessProjection (pairTreeBody (indexedTree ε e).tree) s t))
  rw [Set.image_preimage_eq _ (show Function.Surjective (encodePower n) from
    fun p => ⟨decodePower n p, encode_decodePower n p⟩)]
  exact projected_witnessProjection (indexedTree ε e) s t

/-- Any nonempty refinement by the supplied analytic cell is an actual stronger condition. -/
def refinePowerCondition {ε : ℕ → ℕ} {n : ℕ} (P : PowerCondition ε n)
    (A : Set (Fin (n+1) → (ℕ → ℕ))) (hA : PowerProjected ε n A)
    (hne : (P.val ∩ A).Nonempty) : PowerCondition ε n :=
  ⟨P.val ∩ A, hne, P.property.2.inter hA⟩

theorem refinePowerCondition_le {ε : ℕ → ℕ} {n : ℕ} (P : PowerCondition ε n)
    (A : Set (Fin (n+1) → (ℕ → ℕ))) (hA : PowerProjected ε n A)
    (hne : (P.val ∩ A).Nonempty) : refinePowerCondition P A hA hne ≤ P :=
  Set.inter_subset_left

end LambdaTree
end PolishSpaceBook
