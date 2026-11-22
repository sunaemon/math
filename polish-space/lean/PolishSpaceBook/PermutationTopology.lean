module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

@[expose] public section

/-! # Pointwise convergence on permutations

The topology is induced by evaluation into the product of discrete copies of
`X`. The scoped instance makes this choice explicit. Finite agreement gives
its neighborhood basis, and hence open subgroups at the identity.
-/

namespace PolishSpaceBook.PointwisePerm

open Set Topology Filter

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

/-- Pointwise convergence on a discrete set. -/
scoped instance topology : TopologicalSpace (Equiv.Perm X) :=
  TopologicalSpace.induced (fun p : Equiv.Perm X => (p : X → X)) inferInstance

omit [DiscreteTopology X] in
/-- Forgetting the inverse is a topological embedding. -/
theorem isEmbedding_coe : IsEmbedding (fun p : Equiv.Perm X => (p : X → X)) :=
  ⟨⟨rfl⟩, fun _ _ h => Equiv.ext (congrFun h)⟩

omit [DiscreteTopology X] in
theorem continuous_apply (x : X) : Continuous (fun p : Equiv.Perm X => p x) :=
  (_root_.continuous_apply x).comp isEmbedding_coe.continuous

omit [DiscreteTopology X] in
/-- A map to permutations is continuous precisely when every coordinate is. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → Equiv.Perm X} :
    Continuous f ↔ ∀ x, Continuous (fun y => f y x) := by
  rw [isEmbedding_coe.continuous_iff, continuous_pi_iff]
  rfl

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Inversion is continuous because $\tau^{-1}(x)=y$ is equivalent to $\tau(y)=x$. Multiplication is continuous because
    fixing the values of $\tau$ on $F$ and of $\sigma$ on $\tau(F)$ fixes the values of $\sigma\tau$ on $F$.
-/
/-- Inversion is continuous: specifying an inverse value specifies a forward value. -/
theorem continuous_inverse : Continuous (fun p : Equiv.Perm X => p⁻¹) := by
  apply continuous_iff.mpr
  intro x
  apply continuous_discrete_rng.mpr
  intro y
  have he : {p : Equiv.Perm X | p⁻¹ x = y} = {p | p y = x} := by
    ext p
    exact p.symm_apply_eq.trans eq_comm
  rw [show (fun p : Equiv.Perm X => p⁻¹ x) ⁻¹' {y} = {p | p⁻¹ x = y} from rfl, he]
  exact (isOpen_discrete ({x} : Set X)).preimage (continuous_apply y)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    For the remaining implication, we use the following description of permutation groups on countable sets.
-/
scoped instance topologicalGroup : IsTopologicalGroup (Equiv.Perm X) where
  continuous_inv := continuous_inverse
  continuous_mul := by
    apply continuous_iff.mpr
    intro x
    have hev : Continuous (fun z : (Equiv.Perm X) × X => z.1 z.2) :=
      continuous_prod_of_discrete_right.mpr continuous_apply
    exact hev.comp (continuous_fst.prodMk ((continuous_apply x).comp continuous_snd))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For a countable discrete set $X$, the pointwise-convergence topology on $\mathrm{Sym}(X)$ has basic neighborhoods
    $$N(\sigma,F):=\{\tau\in\mathrm{Sym}(X):\forall x\in F,\ \tau(x)=\sigma(x)\},\quad F\IncludedIn X\text{ finite}.$$
-/
/-- Neighborhoods are exactly supersets of finite-agreement cylinders. -/
theorem mem_nhds_iff {p : Equiv.Perm X} {U : Set (Equiv.Perm X)} :
    U ∈ 𝓝 p ↔ ∃ F : Finset X, {q | ∀ x ∈ F, q x = p x} ⊆ U := by
  classical
  constructor
  · intro hU
    rw [isEmbedding_coe.nhds_eq_comap, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨F, t, ht, hFV⟩ := hV
    refine ⟨F, fun q hq => hVU (hFV ?_)⟩
    intro x hx
    change q x ∈ t x
    rw [hq x hx]
    exact mem_of_mem_nhds (ht x)
  · rintro ⟨F, hF⟩
    apply mem_of_superset _ hF
    have hopen : IsOpen {q : Equiv.Perm X | ∀ x ∈ F, q x = p x} := by
      have he : {q : Equiv.Perm X | ∀ x ∈ F, q x = p x} =
          ⋂ x ∈ F, (fun q : Equiv.Perm X => q x) ⁻¹' {p x} := by ext; simp
      rw [he]
      exact isOpen_biInter_finset fun x _ => (isOpen_discrete _).preimage (continuous_apply x)
    exact hopen.mem_nhds (by simp)

/-- The finite pointwise stabilizer as an open subgroup. -/
def finiteStabilizer (F : Finset X) : OpenSubgroup (Equiv.Perm X) where
  toSubgroup := fixingSubgroup (Equiv.Perm X) (F : Set X)
  isOpen' := by
    have he : (fixingSubgroup (Equiv.Perm X) (F : Set X) : Set (Equiv.Perm X)) =
        ⋂ x ∈ F, (fun p : Equiv.Perm X => p x) ⁻¹' {x} := by
      ext p
      simp [mem_fixingSubgroup_iff, Equiv.Perm.smul_def]
    change IsOpen (fixingSubgroup (Equiv.Perm X) (F : Set X) : Set (Equiv.Perm X))
    rw [he]
    exact isOpen_biInter_finset fun x _ => (isOpen_discrete _).preimage (continuous_apply x)

scoped instance nonarchimedean : NonarchimedeanGroup (Equiv.Perm X) where
  is_nonarchimedean U hU := by
    obtain ⟨F, hF⟩ := mem_nhds_iff.mp hU
    refine ⟨finiteStabilizer F, fun p hp => hF ?_⟩
    change p ∈ fixingSubgroup (Equiv.Perm X) (F : Set X) at hp
    simpa [mem_fixingSubgroup_iff, Equiv.Perm.smul_def] using hp

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] First suppose $H\leq \InfiniteSymmetricGroup$ is closed. The topology of $\InfiniteSymmetricGroup$
    has a neighborhood base at the identity consisting of pointwise stabilizers of finite sets,
    $$\{\sigma\in\InfiniteSymmetricGroup:\restrict{\sigma}{F}=\mathrm{id}_F\}.$$
    Intersecting these stabilizers with $H$ gives a neighborhood base of open subgroups in $H$, so $H$ is non-Archimedean.
-/
/-- Subgroups inherit the finite-stabilizer basis; no closedness is needed. -/
theorem subgroup_nonarchimedean (H : Subgroup (Equiv.Perm X)) : NonarchimedeanGroup H where
  is_nonarchimedean U hU := by
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨W, hWV⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
    exact ⟨W.comap H.subtype continuous_subtype_val, fun p hp => hVU (hWV hp)⟩

/-- Inverse pairs form a closed subset of the product of two function spaces. -/
theorem isClosed_inversePairs :
    IsClosed {fg : (X → X) × (X → X) | (∀ x, fg.1 (fg.2 x) = x) ∧ ∀ x, fg.2 (fg.1 x) = x} := by
  have hev : Continuous (fun z : (X → X) × X => z.1 z.2) :=
    continuous_prod_of_discrete_right.mpr _root_.continuous_apply
  have he : {fg : (X → X) × (X → X) | (∀ x, fg.1 (fg.2 x) = x) ∧ ∀ x, fg.2 (fg.1 x) = x} =
      (⋂ x, {fg | fg.1 (fg.2 x) = x}) ∩ (⋂ x, {fg | fg.2 (fg.1 x) = x}) := by
    ext; simp
  rw [he]
  apply IsClosed.inter <;> apply isClosed_iInter <;> intro x
  · exact isClosed_eq (hev.comp (continuous_fst.prodMk
      ((_root_.continuous_apply x).comp continuous_snd))) continuous_const
  · exact isClosed_eq (hev.comp (continuous_snd.prodMk
      ((_root_.continuous_apply x).comp continuous_fst))) continuous_const

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    The map $\sigma\mapsto(\sigma,\sigma^{-1})$ is a homeomorphism onto
    $$\{(f,h)\in\seqPower{X}{X}\times\seqPower{X}{X}:
      \forall x\in X,\ f(h(x))=x\text{ and }h(f(x))=x\}.$$
    This set is closed: for each $x$, both equations are closed conditions, since evaluation is continuous when $X$
    is discrete. The countable products are Polish, so $\mathrm{Sym}(X)$ is Polish as well.
-/
/-- Adding the inverse coordinate embeds permutations as the closed inverse pairs. -/
theorem isClosedEmbedding_pair :
    IsClosedEmbedding (fun p : Equiv.Perm X => ((p : X → X), ((p⁻¹ : Equiv.Perm X) : X → X))) := by
  have hc : Continuous (fun p : Equiv.Perm X => ((p : X → X), ((p⁻¹ : Equiv.Perm X) : X → X))) :=
    isEmbedding_coe.continuous.prodMk (isEmbedding_coe.continuous.comp continuous_inverse)
  have he : IsEmbedding (fun p : Equiv.Perm X => ((p : X → X), ((p⁻¹ : Equiv.Perm X) : X → X))) :=
    IsEmbedding.of_comp hc continuous_fst isEmbedding_coe
  refine ⟨he, ?_⟩
  have hr : range (fun p : Equiv.Perm X => ((p : X → X), ((p⁻¹ : Equiv.Perm X) : X → X))) =
      {fg | (∀ x, fg.1 (fg.2 x) = x) ∧ ∀ x, fg.2 (fg.1 x) = x} := by
    ext fg
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.apply_symm_apply, p.symm_apply_apply⟩
    · rintro ⟨hr, hl⟩
      exact ⟨⟨fg.1, fg.2, hl, hr⟩, rfl⟩
  rw [hr]
  exact isClosed_inversePairs

scoped instance polishSpace [Countable X] : PolishSpace (Equiv.Perm X) := by
  let : PolishSpace X := by infer_instance
  let : PolishSpace (X → X) := by infer_instance
  let : PolishSpace ((X → X) × (X → X)) := by infer_instance
  exact (isClosedEmbedding_pair (X := X)).polishSpace

/-- Relabeling a discrete set gives a homeomorphism of its permutation group. -/
def relabelHomeomorph {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
    (e : X ≃ Y) : Equiv.Perm X ≃ₜ Equiv.Perm Y where
  toEquiv := e.permCongr
  continuous_toFun := by
    apply continuous_iff.mpr
    intro y
    exact continuous_of_discreteTopology.comp (continuous_apply (e.symm y))
  continuous_invFun := by
    apply continuous_iff.mpr
    intro x
    exact continuous_of_discreteTopology.comp (continuous_apply (e x))

/-- Pulling back finite stabilizers along an embedding gives open subgroups. -/
theorem nonarchimedean_of_embedding {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : G →* Equiv.Perm X) (hf : IsEmbedding f) :
    NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_one, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨W, hWV⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
    exact ⟨W.comap f hf.continuous, fun g hg => hVU (hWV hg)⟩

end PolishSpaceBook.PointwisePerm
