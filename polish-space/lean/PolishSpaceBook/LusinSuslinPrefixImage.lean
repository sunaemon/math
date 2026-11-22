module

public import PolishSpaceBook.LusinSuslinPrefixTests
public import PolishSpaceBook.LambdaLusinSuslinPrefixes

@[expose] public section

/-! # The Borel image formula from separated prefixes and metric neighborhoods -/

namespace PolishSpaceBook
namespace LusinSuslinPrefix

open Set TopologicalSpace Topology MeasureTheory Metric Filter

variable {Y : Type*} [MetricSpace Y] {F : Set baire_space}

def neighborhood (f : F → Y) (s : List ℕ) : Set Y :=
  ⋃ x : F, ⋃ (_ : x.val ∈ cyl s), ball (f x) ((1 / 2 : ℝ) ^ s.length)

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Finally put
    $$
    O_s := \bigcup_{x\in F\cap\cyl{s}}\Ball{f(x)}{2^{-|s|}}.
    $$
    This is an open neighborhood of $A_s$ in $Y$.
-/
theorem neighborhood_open (f : F → Y) (s : List ℕ) : IsOpen (neighborhood f s) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem mem_neighborhood_iff (f : F → Y) (s : List ℕ) (y : Y) :
    y ∈ neighborhood f s ↔ ∃ x : F, x.val ∈ cyl s ∧ dist (f x) y < (1 / 2 : ℝ) ^ s.length := by
  simp only [neighborhood, mem_iUnion, mem_ball, dist_comm, exists_prop]

theorem slice_subset_neighborhood (f : F → Y) (s : List ℕ) : slice f s ⊆ neighborhood f s := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_neighborhood_iff f s (f x)).mpr ⟨x, hx, by simp⟩

def imageTest (f : F → Y) (C : List ℕ → Set Y) : Set Y :=
  ⋂ k : ℕ, ⋃ s : {s : List ℕ // s.length = k + 1},
    compatibleTest C s.val ∩ neighborhood f s.val

/-- Disjoint compatible tests recover a unique input; shrinking neighborhoods recover its output. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    We claim
    \begin{equation*}
    f(F)
    \;=\;
    \bigcap_{k\ge 1}\,
    \bigcup_{s\in\funcspace{k}{\omega}}
    \left(H_s\cap O_s\right).
    \tag{$\dagger$}
    \end{equation*}
    The right-hand side is Borel because it is a countable intersection of countable unions of Borel sets.

    \emph{($\IncludedIn$).} If $y=f(x)$ with $x\in F$, then for each $k\ge 1$ the prefix $s=\restrict{x}{k}$ satisfies $y\in
    A_s\IncludedIn H_s\cap O_s$. Thus $y$ lies in the right-hand side of $(\dagger)$.

    \emph{($\supseteq$).} Let $y$ lie in the right-hand side. For each $k\ge 1$, choose $s_k\in\funcspace{k}{\omega}$ with
    $y\in H_{s_k}\cap O_{s_k}$. The prefix tests make this sequence unique and compatible. Indeed, the sets $H_s$ at level
    $k$ are pairwise disjoint, so there is at most one such $s_k$; and since $H_{s_{k+1}}\IncludedIn
    H_{\restrict{s_{k+1}}{k}}$, disjointness at level $k$ forces $s_k=\restrict{s_{k+1}}{k}$.

    Let $x:=\bigcup_k s_k\in\BaireSpace$. Since $y\in O_{s_k}$, choose $x_k\in F\cap\cyl{s_k}$ with
    $$
    d_Y(f(x_k),y)<2^{-k}.
    $$
    The compatibility of the prefixes gives $x_k\to x$ in $\BaireSpace$, and closedness of $F$ gives $x\in F$. Continuity
    gives $f(x_k)\to f(x)$, while the displayed inequality gives $f(x_k)\to y$. Limits are unique in the metric space $Y$,
    so $y=f(x)$. This proves $(\dagger)$, and consequently $f(F)$ is Borel.
-/
theorem range_eq_imageTest (hF : IsClosed F) {f : F → Y} (hf : Continuous f)
    (C : List ℕ → Set Y) (hC : ∀ s, slice f s ⊆ compatibleTest C s) :
    range f = imageTest f C := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply mem_iInter.mpr
    intro k
    apply mem_iUnion.mpr
    refine ⟨⟨seqPrefix x.val (k + 1), seqPrefix_length _ _⟩, ?_⟩
    have hx : f x ∈ slice f (seqPrefix x.val (k + 1)) := ⟨x, mem_cyl_seqPrefix _ _, rfl⟩
    exact ⟨hC _ hx, slice_subset_neighborhood f _ hx⟩
  · intro hy
    have hs : ∀ k, ∃ s : List ℕ, s.length = k + 1 ∧
        y ∈ compatibleTest C s ∧ y ∈ neighborhood f s := by
      intro k
      obtain ⟨s, hs⟩ := mem_iUnion.mp (mem_iInter.mp hy k)
      exact ⟨s.val, s.property, hs⟩
    choose s hl hc hn using hs
    have hp (n m : ℕ) (hnm : n ≤ m) : prefixOf (s n) (s m) := by
      have he : s n = (s m).take (n + 1) := compatibleTest_unique (hc n)
        (compatibleTest_take (hc m) (n + 1)) (by simp only [hl, List.length_take]; omega)
      rw [he]
      exact List.take_prefix _ _
    let t : ℕ → List ℕ
      | 0 => []
      | n + 1 => s n
    have ht : ∀ n, (t n).length = n := by
      intro n
      cases n with
      | zero => rfl
      | succ n => exact hl n
    have htp : ∀ n m, n ≤ m → prefixOf (t n) (t m) := by
      intro n m hnm
      cases n with
      | zero => exact List.nil_prefix
      | succ n =>
        cases m with
        | zero => omega
        | succ m => exact hp n m (by omega)
    obtain ⟨x, hx⟩ := LambdaTree.sequence_of_prefix_family t ht htp
    have hxs (n : ℕ) : seqPrefix x (n + 1) = s n := hx (n + 1)
    have hz (n : ℕ) := (mem_neighborhood_iff f (s n) y).mp (hn n)
    choose z hzprefix hnear using hz
    have hzlim : Tendsto (fun n => (z n).val) atTop (𝓝 x) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop i] with n hn
      have hz' : (z n).val ∈ cyl (seqPrefix x (n + 1)) := by rw [hxs]; exact hzprefix n
      have hi : i < (seqPrefix x (n + 1)).length := by simp only [seqPrefix_length]; omega
      simpa only [seqPrefix_get] using (hz' i hi).symm
    have hxF : x ∈ F := hF.mem_of_tendsto hzlim (Eventually.of_forall fun n => (z n).property)
    let zlim : F := ⟨x, hxF⟩
    have hzsub : Tendsto z atTop (𝓝 zlim) := tendsto_subtype_rng.mpr hzlim
    have hflim := hf.continuousAt.tendsto.comp hzsub
    have hylim : Tendsto (fun n => f (z n)) atTop (𝓝 y) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hnear n).le)
      simpa only [hl, Function.comp_def] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).comp (tendsto_add_atTop_nat 1)
    exact ⟨zlim, tendsto_nhds_unique hflim hylim⟩

variable [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [PolishSpace Y] in
theorem imageTest_measurable (f : F → Y) {C : List ℕ → Set Y}
    (hC : ∀ s, MeasurableSet (C s)) : MeasurableSet (imageTest f C) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun s =>
    (compatibleTest_measurable hC s.val).inter (neighborhood_open f s.val).measurableSet

/-- The separated-prefix construction of the closed-source case of Lusin--Suslin. -/
theorem measurableSet_range (hF : IsClosed F) {f : F → Y}
    (hf : Continuous f) (hi : Function.Injective f) : MeasurableSet (range f) := by
  obtain ⟨C, hC, hsub, hd⟩ := exists_raw_tests hF hf hi
  rw [range_eq_imageTest hF hf C (slice_subset_compatibleTest hsub hd)]
  exact imageTest_measurable f hC


/-- Apply the closed-source image construction again to each basic clopen of the source. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    It suffices to handle a basic clopen $\cyl{t} \cap F$ with $t \in \finseq{\omega}$. The set $F \cap \cyl{t}$ is closed
    in $\BaireSpace$, and the restriction
    $$
    f|_{F\cap\cyl{t}}:F\cap\cyl{t}\to Y
    $$
    is again continuous and injective. Applying the image part of the closed-subspace case just proved to this restriction
    shows that $f(F\cap\cyl{t})$ is Borel in $Y$.
-/
theorem slice_measurable (hF : IsClosed F) {f : F → Y}
    (hf : Continuous f) (hi : Function.Injective f) (s : List ℕ) :
    MeasurableSet (slice f s) := by
  let G := F ∩ cyl s
  let g : G → Y := fun x => f ⟨x.val, x.property.1⟩
  have hg : Continuous g := hf.comp (continuous_subtype_val.subtype_mk fun x => x.property.1)
  have hgi : Function.Injective g := by
    intro x z he
    have hxz := hi he
    exact Subtype.ext (congrArg (fun a : F => a.val) hxz)
  have hr : range g = slice f s := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.val, x.property.1⟩, x.property.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, x.property, hx⟩, rfl⟩
  rw [← hr]
  exact measurableSet_range (hF.inter (isClosed_cyl s)) hg hgi

/-- The inverse is Borel because the inverse images of domain cylinders are Borel prefix images. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Since
    $$
    (f^{-1})^{-1}(\cyl{t} \cap F)=f(F\cap\cyl{t}),
    $$
    the preimage of every basic clopen of $F$ under $f^{-1}$ is Borel. The basic clopens generate the Borel $\sigma$-algebra
    of $F$, so $f^{-1}$ is Borel.
-/
theorem measurable_inverse (hF : IsClosed F) {f : F → Y}
    (hf : Continuous f) (hi : Function.Injective f) :
    Measurable (Equiv.ofInjective f hi).symm := by
  let e := Equiv.ofInjective f hi
  have hbare : Measurable (fun y : range f => (e.symm y).val) := by
    rw [@BorelSpace.measurable_eq baire_space _ MeasurableSpace.pi _]
    rw [(isTopologicalBasis_cyl (A := ℕ)).borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro _ ⟨s, rfl⟩
    have heq : (fun y : range f => (e.symm y).val) ⁻¹' cyl s = Subtype.val ⁻¹' slice f s := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, Equiv.apply_ofInjective_symm hi y⟩
      · rintro ⟨x, hx, hxy⟩
        have he : x = e.symm y := hi (hxy.trans (Equiv.apply_ofInjective_symm hi y).symm)
        change (e.symm y).val ∈ cyl s
        rw [← he]
        exact hx
    rw [heq]
    exact (slice_measurable hF hf hi s).preimage measurable_subtype_coe
  exact hbare.subtype_mk

/-- The image and the cylinder-based inverse supply the measurable embedding. -/
theorem measurableEmbedding (hF : IsClosed F) {f : F → Y}
    (hf : Continuous f) (hi : Function.Injective f) : MeasurableEmbedding f :=
  MeasurableEmbedding.of_measurable_inverse_on_range hf.measurable
    (measurableSet_range hF hf hi) (measurable_inverse hF hf hi)
    (fun x => Equiv.ofInjective_symm_apply hi x)

end LusinSuslinPrefix
end PolishSpaceBook
