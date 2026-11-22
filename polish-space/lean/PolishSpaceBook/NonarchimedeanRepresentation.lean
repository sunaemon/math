module

public import PolishSpaceBook.PermutationTopology
public import PolishSpaceBook.PolishGroupCategory
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Basic.Denumerable

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The coset action of a non-Archimedean group

Use a decreasing sequence of open subgroups, then let the group act on their
tagged coset spaces. The topology is recovered from the distinguished cosets.
-/

namespace PolishSpaceBook.NonarchimedeanRepresentation

open Set Topology Filter
open scoped PolishSpaceBook.PointwisePerm

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- All open subgroups form an identity-neighborhood basis. -/
theorem openSubgroupBasis :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenSubgroup G => True) (fun V => (V : Set G)) := by
  constructor
  intro U
  constructor
  · intro hU
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean U hU
    exact ⟨V, trivial, hV⟩
  · rintro ⟨V, _, hV⟩
    exact mem_of_superset (V.isOpen.mem_nhds V.one_mem) hV

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    It remains to embed an arbitrary non-Archimedean Polish group. Choose a decreasing countable neighborhood base
    $\Sequence{V_n}{n\in\omega}$
    at the identity consisting of open subgroups with $\bigcap_n V_n=\{e\}$.
    Each quotient $G/V_n$ is discrete and countable,
    since its cosets are pairwise disjoint open subsets of the separable space $G$. Let
    $$X=\ExternalDisjointUnion_{n\in\NN} G/V_n,$$
    a countably infinite set: it is countable as a countable union of countable sets, and the distinguished cosets
    $(n,V_n)$ give an injection of $\NN$ into it. Let $G$ act on $X$ by left translation,
    $$\pi(g)(n,aV_n):=(n,gaV_n).$$
-/
/-- First countability gives a decreasing sequence of open subgroups. -/
theorem exists_openSubgroupSequence [FirstCountableTopology G] :
    ∃ V : ℕ → OpenSubgroup G, (𝓝 (1 : G)).HasAntitoneBasis (fun n => (V n : Set G)) := by
  obtain ⟨V, _, hV⟩ := (openSubgroupBasis (G := G)).exists_antitone_subbasis
  exact ⟨V, hV⟩

/-- The tagged coset spaces used in the book. -/
def CosetSpace (V : ℕ → OpenSubgroup G) := Σ n, G ⧸ (V n).toSubgroup

instance cosetTopology (V : ℕ → OpenSubgroup G) : TopologicalSpace (CosetSpace V) :=
  inferInstanceAs (TopologicalSpace (Σ n, G ⧸ (V n).toSubgroup))

instance discreteCosetSpace (V : ℕ → OpenSubgroup G) : DiscreteTopology (CosetSpace V) := by
  let : ∀ n, DiscreteTopology (G ⧸ (V n).toSubgroup) :=
    fun n => QuotientGroup.discreteTopology (V n).isOpen
  exact inferInstanceAs (DiscreteTopology (Σ n, G ⧸ (V n).toSubgroup))

instance countableCosetSpace [SecondCountableTopology G] (V : ℕ → OpenSubgroup G) :
    Countable (CosetSpace V) := by
  let : ∀ n, DiscreteTopology (G ⧸ (V n).toSubgroup) :=
    fun n => QuotientGroup.discreteTopology (V n).isOpen
  let : ∀ n, Countable (G ⧸ (V n).toSubgroup) :=
    fun n => (TopologicalSpace.separableSpace_iff_countable).mp inferInstance
  exact inferInstanceAs (Countable (Σ n, G ⧸ (V n).toSubgroup))

/-- The identity coset in the nth summand. -/
def baseCoset (V : ℕ → OpenSubgroup G) (n : ℕ) : CosetSpace V :=
  ⟨n, QuotientGroup.mk 1⟩

instance infiniteCosetSpace (V : ℕ → OpenSubgroup G) : Infinite (CosetSpace V) :=
  Infinite.of_injective (baseCoset V) (fun _ _ h => congrArg Sigma.fst h)

/-- Left translation acts within each tagged summand. -/
def cosetAction (V : ℕ → OpenSubgroup G) : G →* Equiv.Perm (CosetSpace V) where
  toFun g :=
    { toFun := fun x => ⟨x.1, g • x.2⟩
      invFun := fun x => ⟨x.1, g⁻¹ • x.2⟩
      left_inv := by rintro ⟨n, x⟩; simp
      right_inv := by rintro ⟨n, x⟩; simp }
  map_one' := by ext ⟨n, x⟩; simp
  map_mul' g h := by ext ⟨n, x⟩; simp [mul_smul]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For each fixed $(n,aV_n)$, this coordinate map is continuous as the composite of right translation by $a$,
    the quotient map, and inclusion into the tagged summand. By the description of the topology above, we obtain a
    continuous homomorphism
    $$\pi:G\to\mathrm{Sym}(X)\cong\InfiniteSymmetricGroup.$$
    It is injective because the intersection of the $V_n$ is trivial. Its topology is the original one because the
    stabilizer of $(n,V_n)$ pulls back to $V_n$: these stabilizers are open in the permutation group, and their
    preimages form a neighborhood base at the identity in $G$. Translating this base recovers the topology at every point.
-/
/-- Each coordinate of the coset action is continuous. -/
theorem continuous_cosetAction (V : ℕ → OpenSubgroup G) : Continuous (cosetAction V) := by
  apply PointwisePerm.continuous_iff.mpr
  rintro ⟨n, x⟩
  exact continuous_sigmaMk.comp (continuous_id.smul continuous_const)

omit [NonarchimedeanGroup G] in
/-- The stabilizer of the distinguished coset is exactly the chosen subgroup. -/
theorem fixes_baseCoset_iff (V : ℕ → OpenSubgroup G) (n : ℕ) (g : G) :
    cosetAction V g (baseCoset V n) = baseCoset V n ↔ g ∈ V n := by
  change (⟨n, g • QuotientGroup.mk (1 : G)⟩ : CosetSpace V) =
    ⟨n, QuotientGroup.mk (1 : G)⟩ ↔ _
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  change (QuotientGroup.mk (g * 1) : G ⧸ (V n).toSubgroup) = QuotientGroup.mk 1 ↔ _
  simp [QuotientGroup.eq]

omit [NonarchimedeanGroup G] in
/-- The intersection of the neighborhood subgroups is trivial in a T₁ group. -/
theorem mem_all_iff_eq_one [T1Space G] (V : ℕ → OpenSubgroup G)
    (hV : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (V n : Set G))) (g : G) :
    (∀ n, g ∈ V n) ↔ g = 1 := by
  constructor
  · intro hg
    by_contra hne
    have hu : ({g}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa [eq_comm] using hne)
    obtain ⟨n, _, hn⟩ := hV.mem_iff.mp hu
    exact hn (hg n) rfl
  · rintro rfl n
    exact (V n).one_mem

omit [NonarchimedeanGroup G] in
/-- Trivial intersection makes the coset action faithful. -/
theorem injective_cosetAction [T1Space G] (V : ℕ → OpenSubgroup G)
    (hV : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (V n : Set G))) :
    Function.Injective (cosetAction V) := by
  apply (injective_iff_map_eq_one (cosetAction V)).mpr
  intro g hg
  apply (mem_all_iff_eq_one V hV g).mp
  intro n
  apply (fixes_baseCoset_iff V n g).mp
  rw [hg]
  rfl

/-- The distinguished stabilizers recover the original topology. -/
theorem isInducing_cosetAction (V : ℕ → OpenSubgroup G)
    (hV : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (V n : Set G))) :
    IsInducing (cosetAction V) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply le_antisymm
  · simpa using ((continuous_cosetAction V).continuousAt (x := 1)).le_comap
  · apply hV.ge_iff.mpr
    intro n _
    rw [Filter.mem_comap]
    refine ⟨{p | p (baseCoset V n) = baseCoset V n}, ?_, ?_⟩
    · exact ((isOpen_discrete ({baseCoset V n} : Set (CosetSpace V))).preimage
        (PointwisePerm.continuous_apply (baseCoset V n))).mem_nhds rfl
    · intro g hg
      exact (fixes_baseCoset_iff V n g).mp hg

/-- The book's coset homomorphism is a topological embedding. -/
theorem isEmbedding_cosetAction [T1Space G] (V : ℕ → OpenSubgroup G)
    (hV : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (V n : Set G))) :
    IsEmbedding (cosetAction V) :=
  ⟨isInducing_cosetAction V hV, injective_cosetAction V hV⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Finally, the preceding paragraph makes $\pi(G)$ a Polish subgroup of $\mathrm{Sym}(X)$ with the inherited topology.
    By \termuse{closedness of Polish subgroups}, its image is closed. Thus $G$ is topologically isomorphic to a closed
    subgroup of $\InfiniteSymmetricGroup$.
-/
/-- Closedness follows from the book's Pettis argument for Polish subgroups. -/
theorem isClosedEmbedding_cosetAction [PolishSpace G] (V : ℕ → OpenSubgroup G)
    (hV : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (V n : Set G))) :
    IsClosedEmbedding (cosetAction V) := by
  have he := isEmbedding_cosetAction V hV
  let : PolishSpace (cosetAction V).range := he.toHomeomorph.symm.isClosedEmbedding.polishSpace
  exact ⟨he, PolishSpaceBook.isClosed_polish_subgroup (cosetAction V).range⟩

/-- Relabel the countably infinite coset set by natural numbers. -/
theorem exists_closedEmbedding_perm_nat [PolishSpace G] :
    ∃ f : G →* Equiv.Perm ℕ, IsClosedEmbedding f := by
  obtain ⟨V, hV⟩ := exists_openSubgroupSequence (G := G)
  let e : CosetSpace V ≃ ℕ := Classical.choice inferInstance
  refine ⟨e.permCongrHom.toMonoidHom.comp (cosetAction V), ?_⟩
  exact (PointwisePerm.relabelHomeomorph e).isClosedEmbedding.comp
    (isClosedEmbedding_cosetAction V hV.toHasBasis)

omit [NonarchimedeanGroup G] in
/-- The first two conditions of the non-Archimedean representation theorem. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{theorem*} For a Polish group $G$, the following are equivalent.
-/
theorem nonarchimedean_iff_closedEmbedding_perm_nat [IsTopologicalGroup G] [PolishSpace G] :
    NonarchimedeanGroup G ↔ ∃ f : G →* Equiv.Perm ℕ, IsClosedEmbedding f := by
  constructor
  · intro hG
    let := hG
    exact exists_closedEmbedding_perm_nat
  · rintro ⟨f, hf⟩
    exact PointwisePerm.nonarchimedean_of_embedding f hf.isEmbedding

end PolishSpaceBook.NonarchimedeanRepresentation
