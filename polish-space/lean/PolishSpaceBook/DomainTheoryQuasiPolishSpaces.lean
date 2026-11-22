module

public import PolishSpaceBook.ComputablePolishSpacesTTE
public import PolishSpaceBook.DomainIntervalBasis
public import PolishSpaceBook.DomainBairePrefixes
public import PolishSpaceBook.DomainBasisChains

@[expose] public section

/-!
# Domain theory and quasi-Polish spaces

Formalization targets for `polish-space/src/polish-space-book/domain-theory-quasi-polish-spaces.md`.

This file formalizes the corrected sequential Smyth-completeness condition and
de Brecht's generalized level-two Borel classes. The imported modules prove the
Scott-continuity equivalence, the flat and powerset examples, and directed
completeness, maximal-element topology, strict endpoint approximation, and
rational basis of the interval domain. They also prove the Baire prefix domain
construction, its finite-word basis, and the topology on maximal elements.
They also establish interpolation through a basis, the Scott-open basis, cofinal
basis chains, the closed chain-name space, and continuity and surjectivity of its
supremum map. This file also proves that the restricted name domain is generalized
Π⁰₂, by continuous inverse image and passage out of a closed subspace.
`DomainRepresentations` completes the continuous name translator and packages
the resulting admissible representation of every designated subspace.
External characterization theorems are marked as such in the source.
-/

namespace PolishSpaceBook

open Set

section QuasiMetric

variable {X : Type*}

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A \termdefine{quasi-metric} on a set $X$ is a function
    $$d:X\times X\to[0,\infty)$$
    such that:
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    1.  $d(x,x)=0$ for every $x$;
    2.  $d(x,z)\le d(x,y)+d(y,z)$ for all $x,y,z$;
    3.  $d(x,y)=d(y,x)=0$ implies $x=y$.
-/
/-- The elementary data and axioms of the quasi-metric used in the book. -/
structure QuasiMetricData (X : Type*) where
  dist : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ dist x y
  refl : ∀ x, dist x x = 0
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  eq_of_both_zero : ∀ {x y}, dist x y = 0 → dist y x = 0 → x = y

/-- The metric symmetrization of a quasi-metric. -/
def QuasiMetricData.symmDist (d : QuasiMetricData X) (x y : X) : ℝ :=
  max (d.dist x y) (d.dist y x)

theorem QuasiMetricData.symmDist_comm (d : QuasiMetricData X) (x y : X) :
    d.symmDist x y = d.symmDist y x := by
  simp [QuasiMetricData.symmDist, max_comm]

theorem QuasiMetricData.symmDist_eq_zero_iff (d : QuasiMetricData X) (x y : X) :
    d.symmDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' : max (d.dist x y) (d.dist y x) = 0 := by
      simpa [QuasiMetricData.symmDist] using h
    have hxy : d.dist x y = 0 := by
      have hle := le_max_left (d.dist x y) (d.dist y x)
      rw [h'] at hle
      exact le_antisymm hle (d.nonneg x y)
    have hyx : d.dist y x = 0 := by
      have hle := le_max_right (d.dist x y) (d.dist y x)
      rw [h'] at hle
      exact le_antisymm hle (d.nonneg y x)
    exact d.eq_of_both_zero hxy hyx
  · rintro rfl
    simp [QuasiMetricData.symmDist, d.refl]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A sequence $\Sequence{x_n}{n\in\omega}$ is \termdefine{left K-Cauchy} if, for every $\varepsilon>0$, there is $N$ such
    that
    $$d(x_n,x_m)<\varepsilon\qquad(N\le n\le m).$$
-/
/-- The oriented Cauchy condition used for sequential Smyth completeness. -/
def LeftKCauchy (d : QuasiMetricData X) (x : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → n ≤ m → d.dist (x n) (x m) < ε

/-- Convergence for the symmetrized metric. -/
def SymmConvergesTo (d : QuasiMetricData X) (x : ℕ → X) (a : X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, d.symmDist (x n) a < ε

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A quasi-metric is \termdefineas{complete quasi-metric}{complete} in the quasi-Polish sense if every left K-Cauchy
    sequence converges with respect to the associated metric
    $$
    \widehat d(x,y):=\max\{d(x,y),d(y,x)\}.
    $$
    This is the sequential form of Smyth completeness: the Cauchy condition is oriented, but its limit must retain the
    information visible in both directions.
-/
/-- Sequential Smyth completeness: every left K-Cauchy sequence converges in
the symmetrized metric. -/
def SmythComplete (d : QuasiMetricData X) : Prop :=
  ∀ x, LeftKCauchy d x → ∃ a, SymmConvergesTo d x a


/-- Forward balls use the orientation in the book: the center is the first argument. -/
def QuasiMetricData.ball (d : QuasiMetricData X) (x : X) (r : ℝ) : Set X :=
  {y | d.dist x y < r}

/-- The triangle inequality gives a smaller forward ball at every point of a ball. -/
theorem QuasiMetricData.ball_refine (d : QuasiMetricData X) {x y : X} {r : ℝ}
    (hy : y ∈ d.ball x r) :
    0 < r - d.dist x y ∧ d.ball y (r - d.dist x y) ⊆ d.ball x r := by
  refine ⟨sub_pos.mpr hy, ?_⟩
  intro z hz
  have htri := d.triangle x y z
  change d.dist y z < r - d.dist x y at hz
  change d.dist x z < r
  linarith

/-- The topology generated by positive-radius forward balls. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Symmetry is not required. The open balls
    $$\Ball{x}{\varepsilon}=\{y:d(x,y)<\varepsilon\}$$
    generate a $T_0$ topology. The asymmetry is intentional: $d(x,y)$ measures how much information is needed to refine $x$
    into $y$, so the cost from $x$ to $y$ need not match the cost from $y$ to $x$.
-/
@[reducible] def QuasiMetricData.topology (d : QuasiMetricData X) : TopologicalSpace X :=
  TopologicalSpace.generateFrom {U | ∃ x r, 0 < r ∧ U = d.ball x r}

/-- Forward balls are already a basis; no finite-intersection enlargement is needed. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Symmetry is not required. The open balls
    $$\Ball{x}{\varepsilon}=\{y:d(x,y)<\varepsilon\}$$
    generate a $T_0$ topology. The asymmetry is intentional: $d(x,y)$ measures how much information is needed to refine $x$
    into $y$, so the cost from $x$ to $y$ need not match the cost from $y$ to $x$.
-/
theorem QuasiMetricData.ball_basis (d : QuasiMetricData X) :
    @TopologicalSpace.IsTopologicalBasis X d.topology
      {U | ∃ x r, 0 < r ∧ U = d.ball x r} := by
  let := d.topology
  refine ⟨?_, ?_, rfl⟩
  · rintro U ⟨x,r,hr,rfl⟩ V ⟨y,s,hs,rfl⟩ z ⟨hzx,hzy⟩
    obtain ⟨hε,hsubε⟩ := d.ball_refine hzx
    obtain ⟨hδ,hsubδ⟩ := d.ball_refine hzy
    let t := min (r - d.dist x z) (s - d.dist y z)
    have ht : 0 < t := lt_min hε hδ
    refine ⟨d.ball z t, ⟨z,t,ht,rfl⟩, ?_, ?_⟩
    · change d.dist z z < t
      rw [d.refl]
      exact ht
    · intro w hw
      change d.dist z w < t at hw
      exact ⟨hsubε ((lt_of_lt_of_le hw (min_le_left _ _))),
        hsubδ ((lt_of_lt_of_le hw (min_le_right _ _)))⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨d.ball x 1, ⟨x,1,by norm_num,rfl⟩, by
      change d.dist x x < 1
      rw [d.refl]
      norm_num⟩

/-- Openness can be tested using balls centered at the point under consideration. -/
theorem QuasiMetricData.isOpen_iff (d : QuasiMetricData X) (U : Set X) :
    @IsOpen X d.topology U ↔ ∀ x ∈ U, ∃ r > 0, d.ball x r ⊆ U := by
  let := d.topology
  rw [d.ball_basis.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨V, ⟨y,r,hr,rfl⟩, hxV, hVU⟩ := h x hx
    obtain ⟨hε,hsub⟩ := d.ball_refine hxV
    exact ⟨_,hε,hsub.trans hVU⟩
  · intro h x hx
    obtain ⟨r,hr,hsub⟩ := h x hx
    exact ⟨d.ball x r, ⟨x,r,hr,rfl⟩, by
      change d.dist x x < r
      rwa [d.refl], hsub⟩

/-- Mutual distance zero is precisely the separation obstruction, so every
quasi-metric topology is T₀, without assuming symmetry or T₁ separation. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Symmetry is not required. The open balls
    $$\Ball{x}{\varepsilon}=\{y:d(x,y)<\varepsilon\}$$
    generate a $T_0$ topology. The asymmetry is intentional: $d(x,y)$ measures how much information is needed to refine $x$
    into $y$, so the cost from $x$ to $y$ need not match the cost from $y$ to $x$.
-/
theorem QuasiMetricData.t0Space (d : QuasiMetricData X) : @T0Space X d.topology := by
  let := d.topology
  apply (t0Space_iff_exists_isOpen_xor_mem X).mpr
  intro x y hxy
  have hne : d.dist x y ≠ 0 ∨ d.dist y x ≠ 0 := by
    by_contra h
    push Not at h
    exact hxy (d.eq_of_both_zero h.1 h.2)
  rcases hne with h | h
  · have hr : 0 < d.dist x y := lt_of_le_of_ne (d.nonneg x y) (Ne.symm h)
    refine ⟨d.ball x (d.dist x y), d.ball_basis.isOpen ⟨x,_,hr,rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · change d.dist x x < d.dist x y
      rwa [d.refl]
    · change ¬ d.dist x y < d.dist x y
      exact lt_irrefl _
  · have hr : 0 < d.dist y x := lt_of_le_of_ne (d.nonneg y x) (Ne.symm h)
    refine ⟨d.ball y (d.dist y x), d.ball_basis.isOpen ⟨y,_,hr,rfl⟩, Or.inr ⟨?_, ?_⟩⟩
    · change d.dist y y < d.dist y x
      rwa [d.refl]
    · change ¬ d.dist y x < d.dist y x
      exact lt_irrefl _

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  excerpt: |
    \begin{definition*} A topological space is \termdefineas{quasi-Polish space}{quasi-Polish} if it is countably based,
    $T_0$, and its topology is induced by some complete quasi-metric.
-/
/-- Quasi-Polish means a countable base, T₀ separation, and a compatible Smyth
complete quasi-metric, rather than mere completeness of the symmetrization. -/
def IsQuasiPolish (X : Type*) [t : TopologicalSpace X] : Prop :=
  SecondCountableTopology X ∧ T0Space X ∧
    ∃ d : QuasiMetricData X, SmythComplete d ∧ d.topology = t

end QuasiMetric

section GeneralizedBorel

variable {X : Type*} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    On the nonmetrizable spaces in this chapter, $\bSigma^0_2$ and $\bPi^0_2$ refer to de Brecht's generalized Borel
    hierarchy [@deBrecht2013]. At level two, $\bSigma^0_2(X)$ consists of the sets
    $$
    \bigcup_n\SetDifference{U_n}{V_n},
    $$
    where every $U_n$ and $V_n$ is open in $X$. Its dual class is
    $$
    \bPi^0_2(X):=\{\SetDifference{X}{A}:A\in\bSigma^0_2(X)\}.
    $$
-/
/-- De Brecht's generalized `Σ⁰₂` class on an arbitrary topological space. -/
def GeneralizedSigma02 (A : Set X) : Prop :=
  ∃ U V : ℕ → Set X,
    (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (V n)) ∧ A = ⋃ n, U n \ V n

/-- The generalized `Π⁰₂` class, defined by complementation. -/
def GeneralizedPi02 (A : Set X) : Prop :=
  GeneralizedSigma02 Aᶜ

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Equivalently, a generalized $\bPi^0_2$ set has the form
    $$
    \bigcap_n\bigl(\SetDifference{X}{U_n}\cup V_n\bigr)
    $$
    for open $U_n,V_n$.
-/
/-- The intersection-of-implications form of generalized `Π⁰₂`. -/
theorem generalizedPi02_iff (A : Set X) :
    GeneralizedPi02 A ↔
      ∃ U V : ℕ → Set X,
        (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (V n)) ∧
          A = ⋂ n, (U n)ᶜ ∪ V n := by
  classical
  constructor
  · rintro ⟨U, V, hU, hV, hA⟩
    refine ⟨U, V, hU, hV, ?_⟩
    ext x
    have hx := Set.ext_iff.mp hA x
    simp only [mem_compl_iff, mem_iUnion, mem_sdiff] at hx
    simp only [mem_iInter, mem_union, mem_compl_iff]
    simpa only [not_not, not_exists, not_and_or] using not_congr hx
  · rintro ⟨U, V, hU, hV, hA⟩
    refine ⟨U, V, hU, hV, ?_⟩
    ext x
    have hx := Set.ext_iff.mp hA x
    simp only [mem_iInter, mem_union, mem_compl_iff] at hx
    simp only [mem_compl_iff, mem_iUnion, mem_sdiff]
    simpa only [not_forall, not_or, not_not] using not_congr hx

/-- Generalized level two is preserved by continuous inverse images. -/
theorem GeneralizedPi02.preimage {Y : Type*} [TopologicalSpace Y]
    {A : Set Y} (hA : GeneralizedPi02 A) {f : X → Y} (hf : Continuous f) :
    GeneralizedPi02 (f ⁻¹' A) := by
  obtain ⟨U,V,hU,hV,rfl⟩ := (generalizedPi02_iff A).mp hA
  apply (generalizedPi02_iff _).mpr
  refine ⟨fun n => f ⁻¹' U n,fun n => f ⁻¹' V n,
    fun n => (hU n).preimage hf,fun n => (hV n).preimage hf,?_⟩
  ext x
  simp

/-- A generalized level-two subset of a closed subspace has the same complexity
in the ambient space. The extra zeroth condition enforces membership in the
closed subspace. -/
theorem GeneralizedPi02.image_subtype_of_isClosed {C : Set X} (hC : IsClosed C)
    {A : Set C} (hA : GeneralizedPi02 A) :
    GeneralizedPi02 (Subtype.val '' A) := by
  classical
  obtain ⟨U,V,hU,hV,hAeq⟩ := (generalizedPi02_iff A).mp hA
  have hUlift (n : ℕ) : ∃ O : Set X, IsOpen O ∧ Subtype.val ⁻¹' O = U n :=
    isOpen_induced_iff.mp (hU n)
  have hVlift (n : ℕ) : ∃ O : Set X, IsOpen O ∧ Subtype.val ⁻¹' O = V n :=
    isOpen_induced_iff.mp (hV n)
  choose O hO hOU using hUlift
  choose P hP hPV using hVlift
  let U' : ℕ → Set X | 0 => Cᶜ | n+1 => O n
  let V' : ℕ → Set X | 0 => ∅ | n+1 => P n
  apply (generalizedPi02_iff _).mpr
  refine ⟨U',V',?_,?_,?_⟩
  · intro n
    cases n with
    | zero => exact hC.isOpen_compl
    | succ n => exact hO n
  · intro n
    cases n with
    | zero => exact isOpen_empty
    | succ n => exact hP n
  · ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      apply mem_iInter.mpr
      intro n
      cases n with
      | zero => exact Or.inl (not_not.mpr a.property)
      | succ n =>
        have han := mem_iInter.mp (hAeq ▸ ha) n
        change a.val ∉ O n ∨ a.val ∈ P n
        have ho : a.val ∈ O n ↔ a ∈ U n := Set.ext_iff.mp (hOU n) a
        have hp : a.val ∈ P n ↔ a ∈ V n := Set.ext_iff.mp (hPV n) a
        exact han.imp (fun h hn => h (ho.mp hn)) hp.mpr
    · intro hx
      have hx0 := mem_iInter.mp hx 0
      have hxc : x ∈ C := by simpa [U',V'] using hx0
      refine ⟨⟨x,hxc⟩,?_,rfl⟩
      rw [hAeq]
      apply mem_iInter.mpr
      intro n
      have hxn := mem_iInter.mp hx (n+1)
      change x ∉ O n ∨ x ∈ P n at hxn
      have ho : x ∈ O n ↔ (⟨x,hxc⟩ : C) ∈ U n := Set.ext_iff.mp (hOU n) ⟨x,hxc⟩
      have hp : x ∈ P n ↔ (⟨x,hxc⟩ : C) ∈ V n := Set.ext_iff.mp (hPV n) ⟨x,hxc⟩
      exact hxn.imp (fun h hn => h (ho.mpr hn)) hp.mp

/-- The designated-subspace condition on closed chain names is generalized Π⁰₂
in the ambient Baire space. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Here are the two closure steps used in this argument. If $f:Y\to Z$ is continuous, then
    $$
    f^{-1}\!\left[\bigcap_n\bigl(\SetDifference{Z}{U_n}\cup V_n\bigr)\right]
    =\bigcap_n\bigl(\SetDifference{Y}{f^{-1}[U_n]}\cup f^{-1}[V_n]\bigr),
    $$
    and the inverse images of the open sets remain open. Next, let $C$ be closed in $Y$ and let
    $A\IncludedIn C$ be generalized $\bPi^0_2$ in the subspace topology. Write its defining relatively open sets as
    $C\cap O_n$ and $C\cap P_n$, where $O_n,P_n$ are open in $Y$. Viewed as a subset of $Y$, it has the following description:
    $$
    A=C\cap\bigcap_n\bigl(\SetDifference{Y}{O_n}\cup P_n\bigr)
    $$
    This still has the required form: use $\SetDifference{Y}{C}$ and $\varnothing$ as the two open sets in the zeroth
    condition, then use $O_n$ and $P_n$ in condition $n+1$. Apply these observations to the closed space of chain names
    and its continuous supremum map.
-/
theorem basisNameDomain_generalizedPi02 {D : Type*} [OmegaCompletePartialOrder D]
    [TopologicalSpace D] [Topology.IsScott D univ] (b : ℕ → D)
    {A : Set D} (hA : GeneralizedPi02 A) :
    GeneralizedPi02 (Subtype.val '' ((basisNameSup b) ⁻¹' A)) :=
  (hA.preimage (basisNameSup_continuous b)).image_subtype_of_isClosed (basisChainNames_isClosed b)

end GeneralizedBorel

end PolishSpaceBook
