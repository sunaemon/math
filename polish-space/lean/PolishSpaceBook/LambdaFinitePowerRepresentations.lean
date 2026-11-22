module

public import PolishSpaceBook.LambdaFinitePowerConditions
public import PolishSpaceBook.RepresentedProducts
public import PolishSpaceBook.RepresentedBaireSpace
public import PolishSpaceBook.LambdaOraclePrograms
public import PolishSpaceBook.LambdaNumericalQueries

@[expose] public section

namespace PolishSpaceBook
open Set Function NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
universe u

/-- The actual finite product representation, including all its valid names. -/
def finitePowerRepresentation {X : Type u} (δ : Representation X) (n : ℕ) :
    Representation (Fin (n+1) → X) where
  domain := {p | ∀ i, decodePower n p i ∈ δ.domain}
  toFun p i := δ.toFun ⟨decodePower n p.val i, p.property i⟩
  surjective := by
    intro x
    choose p hp using (fun i => δ.surjective (x i))
    let names : Fin (n+1) → (ℕ → ℕ) := fun i => (p i).val
    refine ⟨⟨encodePower n names, ?_⟩, ?_⟩
    · intro i
      rw [decode_encodePower]
      exact (p i).property
    · funext i
      simpa only [decode_encodePower] using hp i

/-- A set is represented by all its valid names, not a chosen name per point. -/
def representedNames {X : Type u} (δ : Representation X) (A : Set X) : Set (ℕ → ℕ) :=
  {p | ∃ hp : p ∈ δ.domain, δ.toFun ⟨p, hp⟩ ∈ A}

theorem representedNames_injective {X : Type u} (δ : Representation X) :
    Injective (representedNames δ) := by
  intro A B h
  ext x
  obtain ⟨p, hp⟩ := δ.surjective x
  have he : p.val ∈ representedNames δ A ↔ p.val ∈ representedNames δ B := by rw [h]
  have hmem (C : Set X) : p.val ∈ representedNames δ C ↔ δ.toFun p ∈ C := by
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨p.property, h⟩
  rw [hmem A, hmem B, hp] at he
  exact he

/-- Lightface data on a represented finite power are predicates on its actual names. -/
def RepresentedPowerProjected {X : Type u} (δ : Representation X) (ε : ℕ → ℕ)
    (n : ℕ) (A : Set (Fin (n+1) → X)) : Prop :=
  Projected ε (representedNames (finitePowerRepresentation δ n) A)

/-- Equality of represented sets already identifies all equivalent indices. -/
abbrev RepresentedPowerCondition {X : Type u} (δ : Representation X)
    (ε : ℕ → ℕ) (n : ℕ) :=
  {A : Set (Fin (n+1) → X) // A.Nonempty ∧ RepresentedPowerProjected δ ε n A}

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For a positive integer $d$, let $\GHConditions{d}$ be the partial order of nonempty $\lSigma^1_1$ subsets of $X^d$,
    ordered by inclusion, with smaller sets stronger. Work with indices modulo equality, so this is a countable coded
    partial order.
-/
instance representedPowerCondition_countable {X : Type u} (δ : Representation X)
    (ε : ℕ → ℕ) (n : ℕ) : Countable (RepresentedPowerCondition δ ε n) :=
  (((countable_projected ε).preimage (representedNames_injective (finitePowerRepresentation δ n))).mono
    (fun _ h => h.2)).to_subtype

theorem representedPowerCondition_le_iff {X : Type u} (δ : Representation X)
    (ε : ℕ → ℕ) (n : ℕ) (P Q : RepresentedPowerCondition δ ε n) :
    P ≤ Q ↔ P.val ⊆ Q.val := Iff.rfl

/-- The coordinate decoder is a closed lambda term on the supplied name. -/
def finitePowerCoordinateProgram (n : ℕ) (i : Fin (n+1)) : AlphaTerm :=
  mapOutputProgram (powerProjectionProgram n i) identityProgram

theorem finitePowerCoordinateProgram_runs (n : ℕ) (i : Fin (n+1)) (p : ℕ → ℕ) (k : ℕ) :
    OracleRuns p (finitePowerCoordinateProgram n i) k (decodePower n p i k) := by
  exact mapOutputProgram_runs (powerProjectionProgram_computes n i).1 identityProgram_closed
    (identityProgram_runs p k) ((powerProjectionProgram_computes n i).2 (p k))

theorem finitePowerCoordinate_realizes {X : Type u} (δ : Representation X) (n : ℕ)
    (i : Fin (n+1)) :
    Realizes (finitePowerRepresentation δ n) δ
      (fun p => ⟨decodePower n p.val i, p.property i⟩) (fun x => x i) := fun _ => rfl

theorem finitePowerCoordinateProgram_closed (n : ℕ) (i : Fin (n+1)) :
    (finitePowerCoordinateProgram n i).Closed :=
  mapOutputProgram_closed (powerProjectionProgram_computes n i).1 identityProgram_closed

theorem finitePowerCoordinate_typeTwo (n : ℕ) (i : Fin (n+1)) (D : Set (ℕ → ℕ)) :
    TypeTwoComputes (finitePowerCoordinateProgram n i)
      (fun p : D => decodePower n p.val i) := by
  refine ⟨finitePowerCoordinateProgram_closed n i, ?_⟩
  intro p k m
  constructor
  · intro h
    exact (h.output_unique (finitePowerCoordinateProgram_runs n i p.val k)).symm
  · intro h
    rw [← h]
    exact finitePowerCoordinateProgram_runs n i p.val k

/-- With the identity Baire representation this is the same finite-power pointclass,
not a second independently postulated analytic structure. -/
theorem representedNames_bairePower (n : ℕ) (A : Set (Fin (n+1) → (ℕ → ℕ))) :
    representedNames (finitePowerRepresentation baireIdentityRepresentation n) A = encodePower n '' A := by
  ext p
  constructor
  · rintro ⟨hp, hA⟩
    change decodePower n p ∈ A at hA
    exact ⟨decodePower n p, hA, encode_decodePower n p⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(fun _ => Set.mem_univ _), ?_⟩
    change decodePower n (encodePower n x) ∈ A
    rwa [decode_encodePower]

theorem representedPowerProjected_baire_iff (ε : ℕ → ℕ) (n : ℕ)
    (A : Set (Fin (n+1) → (ℕ → ℕ))) :
    RepresentedPowerProjected baireIdentityRepresentation ε n A ↔ PowerProjected ε n A := by
  unfold RepresentedPowerProjected PowerProjected
  rw [representedNames_bairePower]

/-- A pair condition may retain the entire equivalence relation between its coordinates. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    In particular, a condition in
    $\GHConditions{2}$ may require its two coordinates to be $E$-equivalent.
-/
def representedEquivalencePairCondition {X : Type u} [Nonempty X] (δ : Representation X)
    (ε : ℕ → ℕ) (E : Setoid X)
    (hE : RepresentedPowerProjected δ ε 1 {x | E.r (x 0) (x 1)}) :
    RepresentedPowerCondition δ ε 1 :=
  ⟨{x | E.r (x 0) (x 1)}, ⟨fun _ => Classical.choice inferInstance, E.refl _⟩, hE⟩

/-- Rectangles cannot express arbitrary pair conditions, even equality. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Distinguish $\GHConditions{2}$, whose conditions are arbitrary analytic sets of pairs, from
    $\GHConditions{1}\times\GHConditions{1}$, whose conditions are rectangles.
-/
theorem diagonal_not_rectangle (X : Type u) [Nontrivial X] :
    ¬ ∃ A B : Set X, {x : Fin 2 → X | x 0 = x 1} = {x | x 0 ∈ A ∧ x 1 ∈ B} := by
  rintro ⟨A, B, h⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hx : x ∈ A ∧ x ∈ B := by
    have : (fun _ : Fin 2 => x) ∈ {x : Fin 2 → X | x 0 = x 1} := rfl
    rw [h] at this
    exact this
  have hy : y ∈ A ∧ y ∈ B := by
    have : (fun _ : Fin 2 => y) ∈ {x : Fin 2 → X | x 0 = x 1} := rfl
    rw [h] at this
    exact this
  let v : Fin 2 → X := fun i => if i = 0 then x else y
  have hv : v ∈ {x : Fin 2 → X | x 0 ∈ A ∧ x 1 ∈ B} := by
    change v 0 ∈ A ∧ v 1 ∈ B
    simpa [v] using And.intro hx.1 hy.2
  rw [← h] at hv
  change v 0 = v 1 at hv
  exact hxy (by simpa [v] using hv)

end LambdaTree
end PolishSpaceBook
