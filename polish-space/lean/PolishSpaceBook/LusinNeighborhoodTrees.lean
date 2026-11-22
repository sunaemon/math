module

public import PolishSpaceBook.LambdaEffectiveBoundedness
public import PolishSpaceBook.AnalyticBorelMaps
public import PolishSpaceBook.BorelOrdinalRankLayers

@[expose] public section

/-!
# Neighborhood trees for closed projections

The tree uses the actual metric neighborhoods from the separation proof.
An empty root is retained so that its rank is defined even when all sections
are empty. Coding its open membership tests gives a Borel map to Baire space.
-/

namespace PolishSpaceBook
namespace LusinNeighborhood

open Set TopologicalSpace Topology MeasureTheory Metric Filter

variable {X : Type*} [MetricSpace X]

def nodes (F : Set (X × baire_space)) (x : X) : Set (finseq ℕ) :=
  {s | s = [] ∨ (F ∩ (ball x ((1 / 2 : ℝ) ^ s.length) ×ˢ cyl s)).Nonempty}

theorem nodes_downward (F : Set (X × baire_space)) (x : X) : IsSubtree (nodes F x) := by
  intro s t ht hst
  rcases ht with rfl | ⟨⟨y, p⟩, hF, hy, hp⟩
  · exact Or.inl (List.prefix_nil.mp hst)
  · refine Or.inr ⟨(y, p), hF, ?_, ?_⟩
    · exact lt_of_lt_of_le hy
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hst.length_le)
    · exact (cyl_subset_of_prefix hst) hp

def tree (F : Set (X × baire_space)) (x : X) : RootedPrefixTree where
  tree := nodes F x
  root_mem := Or.inl rfl
  downward := nodes_downward F x

theorem node_open (F : Set (X × baire_space)) (s : finseq ℕ) :
    IsOpen {x | s ∈ nodes F x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  rcases hx with rfl | ⟨⟨y, p⟩, hF, hy, hp⟩
  · have heq : {x | [] ∈ nodes F x} = univ := by ext; simp [nodes]
    rw [heq]
    exact Filter.univ_mem
  · have hxy : x ∈ ball y ((1 / 2 : ℝ) ^ s.length) := by
      simpa only [mem_ball, dist_comm] using hy
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds hxy)
    intro z hz
    exact Or.inr ⟨(y, p), hF, by simpa only [mem_ball, dist_comm] using hz, hp⟩

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    We have
    $$x\in C\quad\Longleftrightarrow\quad T_x\text{ is well-founded}.$$
    Indeed, a witness $\Pair{x}{p}\in F$ gives a branch through $T_x$. Conversely, from a branch $p$ choose, for $n\ge1$,
    $$
    \Pair{x_n}{p_n}\in F\cap\left(\Ball{x}{2^{-n}}\times\cyl{\restrict{p}{n}}\right).
    $$
    The first coordinates converge to $x$ because their distances are less than $2^{-n}$, and every coordinate of $p_n$
    eventually agrees with that of $p$. Hence $\Pair{x_n}{p_n}\to\Pair{x}{p}$, and closedness of $F$ gives $\Pair{x}{p}\in
    F$.
-/
/-- A branch forces witnesses to converge to the required closed section. -/
theorem branch_iff (F : Set (X × baire_space)) (hF : IsClosed F) (x : X) (p : baire_space) :
    p ∈ treeBody (nodes F x) ↔ (x, p) ∈ F := by
  constructor
  · intro hp
    have happrox (n : ℕ) : ∃ z : X × baire_space,
        z ∈ F ∧ dist z.1 x < (1 / 2 : ℝ) ^ (n + 1) ∧ z.2 ∈ cyl (seqPrefix p (n + 1)) := by
      rcases hp (n + 1) with hempty | ⟨z, hz, hnear, hprefix⟩
      · have := congrArg List.length hempty
        simp only [seqPrefix_length, List.length_nil] at this
        omega
      · exact ⟨z, hz, by simpa only [mem_ball, seqPrefix_length] using hnear, hprefix⟩
    choose z hz hnear hprefix using happrox
    have hleft : Tendsto (fun n => (z n).1) atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hnear n).le)
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).comp (tendsto_add_atTop_nat 1)
    have hright : Tendsto (fun n => (z n).2) atTop (𝓝 p) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop i] with n hn
      have hi : i < (seqPrefix p (n + 1)).length := by simp only [seqPrefix_length]; omega
      simpa only [seqPrefix_get] using (hprefix n i hi).symm
    exact hF.mem_of_tendsto (hleft.prodMk_nhds hright) (Eventually.of_forall hz)
  · intro hp n
    exact Or.inr ⟨(x, p), hp, by simp [mem_ball], mem_cyl_seqPrefix p n⟩

noncomputable def code (F : Set (X × baire_space)) (x : X) : baire_space := by
  classical
  exact fun n => if NamedLambda.NatListCode.decode n ∈ nodes F x then 1 else 0

/-- The code tests all prefixes but recovers the same downward-closed tree. -/
theorem treeFromCode_code (F : Set (X × baire_space)) (x : X) :
    LambdaTree.treeFromCode (code F x) = tree F x := by
  classical
  have he : (LambdaTree.treeFromCode (code F x)).tree = (tree F x).tree := by
    ext t
    constructor
    · intro h
      by_cases ht : t = []
      · simpa [ht] using (tree F x).root_mem
      · have hm := h t.length (List.length_pos_iff.mpr ht) le_rfl
        simpa [code, tree] using hm
    · intro ht j _ _
      have ht' : t.take j ∈ nodes F x := (tree F x).downward ht (List.take_prefix j t)
      simp [code, ht']
  have ext : ∀ U V : RootedPrefixTree, U.tree = V.tree → U = V := by
    rintro ⟨u, hu, hru⟩ ⟨v, hv, hrv⟩ rfl
    rfl
  exact ext _ _ he

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    By the \termuse{closed-projection characterization of analytic sets}, choose a closed set
    $F\IncludedIn X\times\BaireSpace$ whose projection is $A_1$, and fix a compatible metric on $X$.
    Retain the empty root and define
    $$
    T_x:=\{\emptySeq\}\cup\left\{s\in\finseq{\omega}:F\cap
    \left(\Ball{x}{2^{-\Length{s}}}\times\cyl{s}\right)\ne\emptyset\right\}.
    $$
    These are trees: passing to an initial segment enlarges both the ball and the cylinder. The added root creates no
    infinite branch. For nonempty $s$, the membership set is open, since
    $$
    \{x:s\in T_x\}
    =\bigcup_{\substack{\Pair{y}{p}\in F\\p\in\cyl{s}}}\Ball{y}{2^{-\Length{s}}}.
    $$
    For the empty word it is all of $X$. Thus the map sending $x$ to the indicator code of $T_x$ is Borel.
-/
theorem code_measurable [MeasurableSpace X] [BorelSpace X] (F : Set (X × baire_space)) :
    Measurable (code F) := by
  classical
  apply Measurable.of_eval
  intro n
  exact Measurable.ite
    (node_open F (NamedLambda.NatListCode.decode n)).measurableSet measurable_const measurable_const

/-- The complement of the closed projection is exactly the well-founded-tree locus. -/
theorem wellFounded_iff (F : Set (X × baire_space)) (hF : IsClosed F) (x : X) :
    WellFounded (strictTreeExtension (tree F x).tree) ↔ x ∉ Prod.fst '' F := by
  rw [← prefixTreeWellFounded_iff _ (tree F x).downward]
  change (¬ ∃ p, p ∈ treeBody (nodes F x)) ↔ _
  simp only [branch_iff F hF]
  constructor
  · intro h ⟨⟨y, p⟩, hp, hxy⟩
    exact h ⟨p, by simpa only [Prod.fst] using hxy ▸ hp⟩
  · intro h ⟨p, hp⟩
    exact h ⟨(x, p), hp, rfl⟩

end LusinNeighborhood
end PolishSpaceBook
