module

public import Mathlib.Topology.Algebra.MulAction
public import PolishSpaceBook.PolishSpaces
public import PolishSpaceBook.PolishGroupCategory
public import PolishSpaceBook.AutomorphismGroups
public import PolishSpaceBook.VaughtTransforms
public import PolishSpaceBook.BeckerKechrisContinuity
public import PolishSpaceBook.BorelCategoryQuantifiers
public import PolishSpaceBook.VaughtBorelRanks
public import PolishSpaceBook.EffrosOrbitMaps
public import PolishSpaceBook.EffrosOrbitRelations
public import PolishSpaceBook.CountableGraphActions
public import PolishSpaceBook.LogicActions
public import PolishSpaceBook.InfinitaryLogic
public import PolishSpaceBook.LopezEscobarBasic
public import PolishSpaceBook.LopezEscobarOpen
public import PolishSpaceBook.LopezEscobarInduction

@[expose] public section

/-!
# Polish groups

Formalization targets for `polish-space/src/polish-space-book/polish-groups.md`.

Formalized here are the elementary group-action facts used in the chapter:
the displayed existential description of orbit equivalence, the fact that it
is an equivalence relation and agrees with mathlib's canonical orbit setoid,
continuity of each orbit map, and closedness of stabilizers for continuous
actions on `T₁` spaces. The imported `PolishGroupCategory` module supplies
Baire-property localization, Pettis, and closedness of Polish subgroups
with the book's category proofs. `VaughtTransforms` supplies the direct and
localized countable-operation rules, both invariance assertions, and the
open-set base cases of the Borel-rank induction. `BorelCategoryQuantifiers`
proves Borelness of both quantifiers by simultaneous induction.
`VaughtBorelRanks` proves preservation of additive and multiplicative levels
and the one-level bound for the opposite polarities.
`EffrosOrbitMaps` supplies the category proof that an orbit nonmeager in
its closure has an open orbit map, and constructs the canonical homeomorphism
from the quotient by the stabilizer onto that orbit.
`EffrosOrbitTheorem` completes the G_delta equivalences, and
`EffrosOrbitRelations` proves the Borel closure-relation formula, the
Borel-orbit-relation corollary, and the common-closure intersection argument.
The later `IndividualOrbitBorel` module applies the book's Lusin--Suslin
construction to prove Borelness of each individual orbit.
These modules expose the Polish-quotient theorem, cited as external
infrastructure in the book, through explicit Polish quotient hypotheses.

`PermutationTopology` and `NonarchimedeanRepresentation` construct the
finite-agreement topology and prove the equivalence between non-Archimedean
Polish groups and closed subgroups of the permutation group on natural numbers.
The construction uses the tagged coset spaces and the preceding Pettis argument.

`AutomorphismGroups` proves closedness of structure automorphism groups, handles
finite universes by extending permutations by the identity, and recovers each
closed subgroup from its positive-arity tuple orbits in a countable relational
language. This completes the three equivalent representation conditions.

`BeckerKechrisContinuity` proves the product-rectangle identity for right-handed
Vaught transforms and continuity in their generated topology for Borel actions.
The cited Polish basis construction is an explicit hypothesis, supplying
Polishness and preservation of the Borel structure, without assuming continuity.

`CountableGraphActions` identifies edge-bit codes with canonical simple graphs,
constructs their Cantor-space presentation and continuous relabeling action,
and proves analyticity of graph isomorphism by projecting the closed witness set.

`LogicActions` constructs the full relation/function-table space, including arity
zero, identifies its codes with canonical first-order structures, and proves
continuity of relabeling, the orbit-isomorphism equivalence, and analyticity
of isomorphism by the same closed-witness projection.

`InfinitaryLogic` defines finite-context infinitary formulas and capture-free
variable renaming, proves continuous term evaluation, and proves that sentence
satisfaction sets are Borel and invariant under isomorphism.

`LopezEscobarBasic` proves the finite-tuple coset basis and constructs the
existential inverse-tuple formulas for finite coordinate diagrams. It verifies
both clopen Vaught transforms, including function values and nullary symbols.

`LopezEscobarOpen` proves that finite diagrams form a basis and reduces open
sets to countable unions of these cylinders. The associated countable
disjunction defines the nonmeager transform of each open set; duality gives
the comeager transform of each closed set.

`LopezEscobarInduction` refines moving cosets by inverse images of finite
initial segments, constructs the comeager formula from the nonmeager formulas,
and closes the simultaneous Borel induction. The empty target tuple gives an
infinitary sentence defining each invariant Borel class, completing the local
Lopez--Escobar proof. The cited Polish-quotient theorem and the turbulence
results are external infrastructure and are explicitly skipped in the source.
-/

namespace PolishSpaceBook

open Set

universe u v

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    For a Borel action of a Polish group $G$ on a standard Borel space $X$, the
    \termdefine{orbit equivalence relation} is
    $$\OrbitER{G}{X} := \{(x, y) \in X \times X : y = g \cdot x \text{ for some } g \in G\}.$$
-/
/-- The orbit-equivalence predicate in the orientation used by the book. -/
def OrbitEquivalent (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x y : X) : Prop :=
  ∃ g : G, y = g • x

/-- Every point is orbit equivalent to itself. -/
theorem orbitEquivalent_refl (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x : X) : OrbitEquivalent G X x x :=
  ⟨1, by simp⟩

/-- Orbit equivalence is symmetric, with the inverse group element as witness. -/
theorem orbitEquivalent_symm (G : Type u) (X : Type v) [Group G] [MulAction G X]
    {x y : X} (hxy : OrbitEquivalent G X x y) : OrbitEquivalent G X y x := by
  rcases hxy with ⟨g, rfl⟩
  exact ⟨g⁻¹, by simp⟩

/-- Orbit equivalence is transitive, with the product of the two witnesses. -/
theorem orbitEquivalent_trans (G : Type u) (X : Type v) [Group G] [MulAction G X]
    {x y z : X} (hxy : OrbitEquivalent G X x y) (hyz : OrbitEquivalent G X y z) :
    OrbitEquivalent G X x z := by
  rcases hxy with ⟨g, rfl⟩
  rcases hyz with ⟨h, rfl⟩
  exact ⟨h * g, by simp [mul_smul]⟩

/-- The displayed orbit predicate is an equivalence relation. -/
theorem orbitEquivalent_equivalence (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    Equivalence (OrbitEquivalent G X) :=
  ⟨orbitEquivalent_refl G X, orbitEquivalent_symm G X, orbitEquivalent_trans G X⟩

/-- The book's orientation of orbit equivalence agrees with mathlib's canonical
orbit setoid. -/
theorem orbitEquivalent_iff_orbitRel (G : Type u) (X : Type v) [Group G] [MulAction G X]
    {x y : X} : OrbitEquivalent G X x y ↔ MulAction.orbitRel G X x y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp⟩
  · rintro ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← hg]
    simp

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    The stabilizer $G_x$ is closed in $G$ as the preimage of $\{x\}$ under the continuous map $g
    \mapsto g \cdot x$.
-/
/-- The orbit map of a continuous action is continuous. -/
theorem continuous_orbitMap
    {G : Type u} {X : Type v} [TopologicalSpace G] [TopologicalSpace X]
    [Group G] [MulAction G X] [ContinuousSMul G X] (x : X) :
    Continuous (fun g : G ↦ g • x) := by
  fun_prop

/-- Stabilizers of continuous actions on `T₁` spaces are closed. -/
theorem isClosed_stabilizer
    {G : Type u} {X : Type v} [TopologicalSpace G] [TopologicalSpace X]
    [Group G] [MulAction G X] [ContinuousSMul G X] [T1Space X] (x : X) :
    IsClosed (MulAction.stabilizer G x : Set G) := by
  rw [show (MulAction.stabilizer G x : Set G) =
      (fun g : G ↦ g • x) ⁻¹' ({x} : Set X) by
    ext g
    simp]
  exact isClosed_singleton.preimage (continuous_orbitMap x)

section Turbulence

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- Finite directed reachability by moves in `V`, with each new point in `U`. -/
inductive LocalOrbitReachable (x : X) (U : Set X) (V : Set G) : X → Prop
  | base : LocalOrbitReachable x U V x
  | step {y : X} (hy : LocalOrbitReachable x U V y) (g : G)
      (hg : g ∈ V) (hgy : g • y ∈ U) : LocalOrbitReachable x U V (g • y)

/-- The local orbit is the least set containing the point and closed under legal moves. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    Fix a continuous action of a Polish group $G$ on a nonempty Polish space $X$. For $x \in X$, an open $U
    \IncludedIn X$ with $x
    \in
    U$, and an open $V \IncludedIn G$ with $e \in V$, the \termdefine{local orbit} $\mathcal O(x, U, V)$ is the smallest set
    containing $x$ with the closure property
    $$y \in \mathcal O(x, U, V) \text{ and } g \in V \text{ and } g \cdot y \in U \;\Longrightarrow\; g \cdot y \in \mathcal
    O(x, U, V).$$
-/
def localOrbit (x : X) (U : Set X) (V : Set G) : Set X :=
  {y | LocalOrbitReachable x U V y}

lemma mem_localOrbit (x : X) (U : Set X) (V : Set G) : x ∈ localOrbit x U V :=
  .base

lemma smul_mem_localOrbit {x y : X} {U : Set X} {V : Set G}
    (hy : y ∈ localOrbit x U V) (g : G) (hg : g ∈ V) (hgy : g • y ∈ U) :
    g • y ∈ localOrbit x U V :=
  LocalOrbitReachable.step hy g hg hgy

/-- The finite-move construction has exactly the minimality required in the book. -/
lemma localOrbit_minimal {x : X} {U A : Set X} {V : Set G} (hx : x ∈ A)
    (hA : ∀ y ∈ A, ∀ g ∈ V, g • y ∈ U → g • y ∈ A) :
    localOrbit x U V ⊆ A := by
  intro y hy
  induction hy with
  | base => exact hx
  | step hy g hg hgy ih => exact hA _ ih g hg hgy

lemma localOrbit_subset {x : X} {U : Set X} {V : Set G} (hx : x ∈ U) :
    localOrbit x U V ⊆ U :=
  localOrbit_minimal hx (fun _ _ _ _ h => h)

variable [TopologicalSpace G] [TopologicalSpace X]

/-- Every local orbit at the point is somewhere dense. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A point $x \in X$ is a \termdefine{turbulent point} if condition (3) holds locally at $x$ — for every $U \ni x$ and $V
    \ni e$, the local orbit $\mathcal O(x, U, V)$ is somewhere dense.
-/
def IsTurbulentPoint (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U →
    ∀ V : Set G, IsOpen V → (1 : G) ∈ V →
      (interior (closure (localOrbit x U V))).Nonempty

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: definition
  title: Hjorth
-/
/-- The book's three conditions for a turbulent action. The intended setting is
 a continuous action of a Polish group on a nonempty Polish space. -/
def IsTurbulentAction : Prop :=
  (∀ x : X, Dense (MulAction.orbit G x)) ∧
    (∀ x : X, IsMeagre (MulAction.orbit G x)) ∧
      ∀ x : X, IsTurbulentPoint (G := G) x

end Turbulence

section EffrosAssembly
open Topology

variable {G : Type*} {X : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [PolishSpace G] [TopologicalSpace X] [PolishSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: theorem
  title: Effros
-/
/-- Assemble all three conditions of Effros from the cited theorem on
Polish quotients by closed subgroups. Closedness of the stabilizer is
discharged here, rather than being assumed separately for each orbit. -/
theorem effros_orbit_theorem_from_polish_quotients
    (hQ : ∀ H : Subgroup G, IsClosed (H : Set G) → PolishSpace (G ⧸ H))
    (x : X) :
    ((¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x)))) ↔
      IsGδ (MulAction.orbit G x)) ∧
    (IsGδ (MulAction.orbit G x) ↔
      IsHomeomorph (MulAction.orbitEquivQuotientStabilizer G x).symm) := by
  have := hQ (MulAction.stabilizer G x) (isClosed_stabilizer x)
  exact ⟨effros_nonmeagre_iff_isGdelta x, effros_isGdelta_iff_quotient_homeomorph x⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{corollary*} If every orbit of a continuous Polish-group action is non-meager in its closure, then
    $\OrbitER{G}{X}$ is
    Borel.

    \end{corollary*}
-/
/-- Apply the same cited quotient theorem to all stabilizers in the
Borel-orbit-relation corollary. -/
theorem measurableSet_orbitRelation_from_polish_quotients
    [MeasurableSpace X] [BorelSpace X]
    (hQ : ∀ H : Subgroup G, IsClosed (H : Set G) → PolishSpace (G ⧸ H))
    (hN : ∀ x : X, ¬ IsMeagre
      (Subtype.val ⁻¹' MulAction.orbit G x : Set (closure (MulAction.orbit G x)))) :
    MeasurableSet {p : X × X | p.2 ∈ MulAction.orbit G p.1} :=
  measurableSet_orbitRelation_of_nonmeagre
    (fun x => hQ (MulAction.stabilizer G x) (isClosed_stabilizer x)) hN

end EffrosAssembly
end PolishSpaceBook
