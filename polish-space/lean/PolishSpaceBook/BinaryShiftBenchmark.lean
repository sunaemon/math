module

public import PolishSpaceBook.PolishGroups
public import Mathlib.SetTheory.Cardinal.Free

@[expose] public section

namespace PolishSpaceBook.BinaryShift
open Set Topology Filter MeasureTheory
universe u
variable (G : Type u) [Group G]

/-- The binary left shift acts by inverse translation of the coordinate. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
scoped instance action : MulAction G (G → Bool) where
  smul g x h := x (g⁻¹ * h)
  one_smul x := by
    funext h
    change x ((1 : G)⁻¹ * h) = x h
    simp
  mul_smul g h x := by
    funext k
    change x ((g * h)⁻¹ * k) = x (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

attribute [local instance] action

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
@[simp] theorem shift_apply (g : G) (x : G → Bool) (h : G) :
    (g • x) h = x (g⁻¹ * h) := rfl

/-- Every coordinate of a fixed shift is a coordinate evaluation. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
theorem continuous_shift (g : G) : Continuous (fun x : G → Bool => g • x) :=
  continuous_pi fun h => continuous_apply (g⁻¹ * h)

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
scoped instance continuousAction [TopologicalSpace G] [DiscreteTopology G] :
    ContinuousSMul G (G → Bool) where
  continuous_smul := continuous_prod_of_discrete_left.mpr fun g => continuous_shift G g

/-- The orbit equivalence relation of the specified shift action. -/
def relation (x y : G → Bool) : Prop := ∃ g : G, y = g • x

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
theorem relation_equivalence : Equivalence (relation G) :=
  orbitEquivalent_equivalence G (G → Bool)

omit [Group G] in
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
theorem shiftSpace_compact_polish [Countable G] :
    CompactSpace (G → Bool) ∧ PolishSpace (G → Bool) := by
  let : PolishSpace Bool := bool_polish
  exact ⟨inferInstance, inferInstance⟩

local instance : MeasurableSpace (G → Bool) := borel _
local instance : BorelSpace (G → Bool) := ⟨rfl⟩

/-- A countable union of the closed graphs of the fixed shifts is Borel. -/
theorem measurableSet_relation [Countable G] :
    MeasurableSet {p : (G → Bool) × (G → Bool) | relation G p.1 p.2} := by
  have heq : {p : (G → Bool) × (G → Bool) | relation G p.1 p.2} =
      ⋃ g : G, {p : (G → Bool) × (G → Bool) | p.2 = g • p.1} := by
    ext p
    simp [relation]
  rw [heq]
  apply MeasurableSet.iUnion
  intro g
  exact (isClosed_eq continuous_snd ((continuous_shift G g).comp continuous_fst)).measurableSet

theorem relation_class_countable [Countable G] (x : G → Bool) :
    {y | relation G x y}.Countable := by
  have heq : {y | relation G x y} = range (fun g : G => g • x) := by
    ext y
    simp [relation, eq_comm]
  rw [heq]
  exact Set.countable_range _

/-- The two generators specify F2. Universality of the following orbit relation
is the cited DJK theorem, not an axiom or an unproved theorem in this module. -/
abbrev FreeTwo := FreeGroup (Fin 2)


/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $F_2$ act by shift on $2^{F_2}$,
    $$
    (g\cdot x)(h)=x(g^{-1}h),
    $$
    on the entire shift space.
-/
theorem freeTwo_shiftSpace_compact_polish :
    CompactSpace (FreeTwo → Bool) ∧ PolishSpace (FreeTwo → Bool) :=
  shiftSpace_compact_polish FreeTwo

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Its orbit relation $\UniversalCountableER$
-/
def universalCountableER : (FreeTwo → Bool) → (FreeTwo → Bool) → Prop := relation FreeTwo

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Its orbit relation $\UniversalCountableER$
-/
theorem universalCountableER_equivalence : Equivalence universalCountableER :=
  relation_equivalence FreeTwo

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Its orbit relation $\UniversalCountableER$
-/
theorem universalCountableER_borel :
    MeasurableSet {p : (FreeTwo → Bool) × (FreeTwo → Bool) | universalCountableER p.1 p.2} :=
  measurableSet_relation FreeTwo

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Its orbit relation $\UniversalCountableER$
-/
theorem universalCountableER_countable (x : FreeTwo → Bool) :
    {y | universalCountableER x y}.Countable :=
  relation_class_countable FreeTwo x

end PolishSpaceBook.BinaryShift
