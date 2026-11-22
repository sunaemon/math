module

public import PolishSpaceBook.PolishGroups
public import PolishSpaceBook.PolishGroupProse
public import PolishSpaceBook.LusinScopeFacts
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

noncomputable section
namespace PolishSpaceBook.PolishGroupScopeFacts
open Set Function Topology Filter TopologicalSpace MeasureTheory
open scoped PointwisePerm

/-- The canonical Boolean-ring addition is coordinatewise addition modulo two. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{Cantor group}: $\CantorSpace$ with coordinate-wise addition modulo $2$ and the product topology.
        It is a compact Polish abelian group. Requiring finitely many coordinates to be $0$ gives its basic open
        subgroups at the identity.
-/
theorem cantor_add_apply (x y : ℕ → Bool) (n : ℕ) :
    (x + y) n = Bool.xor (x n) (y n) := rfl

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{Cantor group}: $\CantorSpace$ with coordinate-wise addition modulo $2$ and the product topology.
        It is a compact Polish abelian group. Requiring finitely many coordinates to be $0$ gives its basic open
        subgroups at the identity.
-/
theorem cantor_compact_polish_addGroup :
    CompactSpace (ℕ → Bool) ∧ PolishSpace (ℕ → Bool) ∧
      IsTopologicalAddGroup (ℕ → Bool) := by
  exact ⟨cantor_space_compact, cantor_space_polish, inferInstance⟩

/-- Finite zero-coordinate requirements form actual open additive subgroups. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{Cantor group}: $\CantorSpace$ with coordinate-wise addition modulo $2$ and the product topology.
        It is a compact Polish abelian group. Requiring finitely many coordinates to be $0$ gives its basic open
        subgroups at the identity.
-/
def cantorZeroSubgroup (F : Finset ℕ) : OpenAddSubgroup (ℕ → Bool) where
  carrier := {x | ∀ n ∈ F, x n = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy n hn
    simp only [Pi.add_apply, hx n hn, hy n hn, add_zero]
  neg_mem' := by
    intro x hx n hn
    simp only [Pi.neg_apply, hx n hn, neg_zero]
  isOpen' := by
    have he : {x : ℕ → Bool | ∀ n ∈ F, x n = 0} =
        ⋂ n ∈ F, (fun x : ℕ → Bool => x n) ⁻¹' {0} := by ext x; simp
    rw [he]
    exact isOpen_biInter_finset fun n _ =>
      (isOpen_discrete ({0} : Set Bool)).preimage (continuous_apply n)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{Cantor group}: $\CantorSpace$ with coordinate-wise addition modulo $2$ and the product topology.
        It is a compact Polish abelian group. Requiring finitely many coordinates to be $0$ gives its basic open
        subgroups at the identity.
-/
theorem cantor_zeroSubgroups_nhds (U : Set (ℕ → Bool)) :
    U ∈ 𝓝 (0 : ℕ → Bool) ↔ ∃ F : Finset ℕ, (cantorZeroSubgroup F : Set _) ⊆ U := by
  classical
  constructor
  · intro hU
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨F, t, ht, hFU⟩ := hU
    refine ⟨F, fun x hx => hFU ?_⟩
    intro n hn
    change x n ∈ t n
    rw [hx n hn]
    exact mem_of_mem_nhds (ht n)
  · rintro ⟨F, hF⟩
    exact mem_of_superset ((cantorZeroSubgroup F).isOpen.mem_nhds
      (cantorZeroSubgroup F).zero_mem) hF

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{Cantor group}: $\CantorSpace$ with coordinate-wise addition modulo $2$ and the product topology.
        It is a compact Polish abelian group. Requiring finitely many coordinates to be $0$ gives its basic open
        subgroups at the identity.
-/
theorem cantor_nonarchimedean : NonarchimedeanAddGroup (ℕ → Bool) where
  is_nonarchimedean U hU := by
    obtain ⟨F, hF⟩ := (cantor_zeroSubgroups_nhds U).mp hU
    exact ⟨cantorZeroSubgroup F, hF⟩

/-- Every finite permutation is extended by the identity outside its finite domain. -/
def finitePermutation (F : Finset ℕ) (p : Equiv.Perm F) : Equiv.Perm ℕ :=
  p.viaFintypeEmbedding ⟨Subtype.val, Subtype.val_injective⟩

theorem finitePermutation_fixed_outside (F : Finset ℕ) (p : Equiv.Perm F)
    {n : ℕ} (hn : n ∉ F) : finitePermutation F p n = n := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  simpa using hn

/-- Complete a finite partial bijection inside F union p(F), then extend by
identity. This gives a genuinely finite-support permutation in each cylinder. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem exists_finitePermutation_agree (p : Equiv.Perm ℕ) (F : Finset ℕ) :
    ∃ (K : Finset ℕ) (r : Equiv.Perm K), ∀ n ∈ F, finitePermutation K r n = p n := by
  classical
  let K := F ∪ F.image p
  let i : F → K := fun x => ⟨x.val, Finset.mem_union_left _ x.property⟩
  let j : F → K := fun x => ⟨p x.val,
    Finset.mem_union_right _ (Finset.mem_image_of_mem p x.property)⟩
  have hi : Injective i := fun x y h => Subtype.ext (congrArg (fun z : K => z.val) h)
  have hj : Injective j := fun x y h => Subtype.ext (p.injective (congrArg (fun z : K => z.val) h))
  obtain ⟨r, hr⟩ := Equiv.Perm.exists_extending_pair i j hi hj
  refine ⟨K, r, fun n hn => ?_⟩
  have h := congrArg Subtype.val (hr ⟨n, hn⟩)
  let e : K ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  change r.viaFintypeEmbedding e (e (i ⟨n, hn⟩)) = p n
  rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
  exact h

/-- A countable family of finite permutations; no arbitrary dense set is assumed. -/
def finitePermutationFamily (z : Σ F : Finset ℕ, Equiv.Perm F) : Equiv.Perm ℕ :=
  finitePermutation z.1 z.2

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem finitePermutationFamily_countable : (range finitePermutationFamily).Countable :=
  Set.countable_range _

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem finitePermutationFamily_dense : Dense (range finitePermutationFamily) := by
  intro p
  apply mem_closure_iff_nhds.mpr
  intro U hU
  obtain ⟨F, hF⟩ := PointwisePerm.mem_nhds_iff.mp hU
  obtain ⟨K, r, hr⟩ := exists_finitePermutation_agree p F
  exact ⟨finitePermutation K r, hF hr, ⟨⟨K, r⟩, rfl⟩⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem finitePermutationFamily_finite_support {p : Equiv.Perm ℕ}
    (hp : p ∈ range finitePermutationFamily) : {n | p n ≠ n}.Finite := by
  obtain ⟨⟨F, r⟩, rfl⟩ := hp
  apply F.finite_toSet.subset
  intro n hn
  by_contra hnot
  exact hn (finitePermutation_fixed_outside F r hnot)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem finitary_permutations_dense : Dense {p : Equiv.Perm ℕ | {n | p n ≠ n}.Finite} :=
  finitePermutationFamily_dense.mono (fun _ hp => finitePermutationFamily_finite_support hp)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem permutation_separable_from_finitary : SeparableSpace (Equiv.Perm ℕ) :=
  ⟨range finitePermutationFamily, finitePermutationFamily_countable, finitePermutationFamily_dense⟩

/-- Discreteness turns coordinate convergence into eventual agreement;
inversion is continuous for precisely this pointwise topology. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem permutation_sequence_converges_iff (s : ℕ → Equiv.Perm ℕ) (p : Equiv.Perm ℕ) :
    Tendsto s atTop (𝓝 p) ↔
      (∀ k, ∀ᶠ n in atTop, s n k = p k) ∧
      (∀ k, ∀ᶠ n in atTop, (s n)⁻¹ k = p⁻¹ k) := by
  constructor
  · intro hs
    constructor
    · intro k
      simpa only [Function.comp_apply, nhds_discrete, tendsto_pure] using (PointwisePerm.continuous_apply k).tendsto p |>.comp hs
    · intro k
      simpa only [Function.comp_apply, nhds_discrete, tendsto_pure] using
        ((PointwisePerm.continuous_apply k).comp PointwisePerm.continuous_inverse).tendsto p |>.comp hs
  · rintro ⟨hs, _⟩
    apply PointwisePerm.isEmbedding_coe.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro k
    simpa only [Function.comp_apply, nhds_discrete, tendsto_pure] using hs k

/-- The closed inverse-pair construction supplies a compatible complete metric. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
        $g_n \to g$
        iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
        witnessing separability; a complete metric is built coordinate-wise.
-/
theorem permutation_polish_from_inverse_pairs : PolishSpace (Equiv.Perm ℕ) :=
  PointwisePerm.isClosedEmbedding_pair.polishSpace

/-- The earlier finite-coordinate closedness proof supplies the canonical
Polish topology on a countable structure's actual automorphism subgroup. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\mathrm{Aut}(M)$ for a countable first-order structure $M$ in the sense of Appendix
        §{sec:appendix-logic}, with the subspace topology from $\InfiniteSymmetricGroup$. This gives the natural
        Polish-group structure on automorphism groups of countable structures.
-/
theorem automorphism_subgroup_polish (L : FirstOrder.Language) (M : Type*)
    [L.Structure M] [TopologicalSpace M] [DiscreteTopology M] [Countable M] :
    PolishSpace (AutomorphismGroups.automorphismSubgroup L M) :=
  AutomorphismGroups.automorphism_polishSpace L M

section BorelStructure
universe u v
variable {X : Type u} {Y : Type v}

/-- Equal Borel structures preserve the same reduction map and its relation law. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This change preserves the $\sigma$-algebra, the orbit equivalence relation,
    and Borel reducibility.
-/
theorem borelReduces_iff_of_borel_eq
    (t t' : TopologicalSpace X) (s s' : TopologicalSpace Y)
    (hX : @borel X t = @borel X t') (hY : @borel Y s = @borel Y s')
    (E : X → X → Prop) (F : Y → Y → Prop) (f : X → Y) :
    @BorelReduces X Y (@borel X t) (@borel Y s) E F f ↔
      @BorelReduces X Y (@borel X t') (@borel Y s') E F f := by
  rw [hX, hY]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This change preserves the $\sigma$-algebra, the orbit equivalence relation,
    and Borel reducibility.
-/
theorem borelReducible_iff_of_borel_eq
    (t t' : TopologicalSpace X) (s s' : TopologicalSpace Y)
    (hX : @borel X t = @borel X t') (hY : @borel Y s = @borel Y s')
    (E : X → X → Prop) (F : Y → Y → Prop) :
    @BorelReducible X Y (@borel X t) (@borel Y s) E F ↔
      @BorelReducible X Y (@borel X t') (@borel Y s') E F := by
  rw [hX, hY]

/-- With the action unchanged, identity preserves every orbit, and is a
Borel reduction in both directions between the two presentations. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This change preserves the $\sigma$-algebra, the orbit equivalence relation,
    and Borel reducibility.
-/
theorem orbit_identity_borelReduces {G : Type*} [Group G] [MulAction G X]
    (t t' : TopologicalSpace X) (hX : @borel X t = @borel X t') :
    @BorelReduces X X (@borel X t) (@borel X t')
      (OrbitEquivalent G X) (OrbitEquivalent G X) id ∧
    @BorelReduces X X (@borel X t') (@borel X t)
      (OrbitEquivalent G X) (OrbitEquivalent G X) id := by
  constructor
  · rw [← hX]
    exact ⟨measurable_id, fun _ _ => Iff.rfl⟩
  · rw [hX]
    exact ⟨measurable_id, fun _ _ => Iff.rfl⟩
end BorelStructure

/-- Only the logical consequence is local: the two cited external inputs are
Hjorth's obstruction and universal closed-subgroup logic-action coding. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently no such action can satisfy all three turbulence hypotheses.
-/
theorem not_turbulent_of_external_classification
    (H : Subgroup (Equiv.Perm ℕ)) (hH : IsClosed (H : Set (Equiv.Perm ℕ)))
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [Nonempty X]
    [MulAction H X] [ContinuousSMul H X] [MeasurableSpace X] [BorelSpace X]
    (hcoding : ∀ K : Subgroup (Equiv.Perm ℕ), IsClosed (K : Set (Equiv.Perm ℕ)) →
      ∀ (a : MulAction K X), letI := a
      ContinuousSMul K X →
      PolishGroupProse.ClassifiableByCountableStructures (OrbitEquivalent K X))
    (hhjorth : IsTurbulentAction (G := H) (X := X) →
      ¬ PolishGroupProse.ClassifiableByCountableStructures (OrbitEquivalent H X)) :
    ¬ IsTurbulentAction (G := H) (X := X) := by
  intro ht
  exact hhjorth ht (hcoding H hH inferInstance inferInstance)

end PolishSpaceBook.PolishGroupScopeFacts
