module

public import Mathlib.SetTheory.Ordinal.FixedPointApproximants
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Bases

@[expose] public section

/-! # The transfinite Cantor--Bendixson construction

The recursion intersects the original closed set with the derivatives of all
predecessor stages. Its initial, successor and limit equations identify it
with the book's transfinite derivative. No decomposition theorem is used.
-/

namespace PolishSpaceBook.CantorBendixson
open Set Order TopologicalSpace
universe u
variable {X : Type u} [TopologicalSpace X]

/-- The book removes only isolated points belonging to the original set. -/
def relativeDerivative (A : Set X) : Set X := A ∩ derivedSet A

/-- The relative derivative has the book's open-neighborhood definition. -/
theorem mem_relativeDerivative_iff {A : Set X} {x : X} :
    x ∈ relativeDerivative A ↔ x ∈ A ∧
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A \ {x})).Nonempty := by
  change (x ∈ A ∧ x ∈ derivedSet A) ↔ _
  rw [mem_derivedSet, accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt,
    mem_closure_iff]

/-- A closed set contains all its accumulation points, so the definitions agree. -/
theorem relativeDerivative_eq_derivedSet {A : Set X} (hA : IsClosed A) :
    relativeDerivative A = derivedSet A :=
  inter_eq_right.mpr ((isClosed_iff_derivedSet_subset A).mp hA)

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] For a subset $A$ of a topological space, define the
    \emph{\termdefineas{Cantor--Bendixson derivative}{Cantor–Bendixson derivative}} $\cbderivative{A}$ to be the set of
    points $x\in A$ such that every open neighborhood of $x$ meets $\SetDifference{A}{\{x\}}$. Thus it is $A$ with
    its isolated points removed. Some authors instead define $\cbderivative{A}$ as the set of \emph{all}
    limit points of $A$, including those outside $A$; the two definitions coincide when $A$ is closed, which is the only
    case used here. In a $T_1$ space, if $A$ is closed then so is $\cbderivative{A}$, and $A$ is perfect precisely when $A =
    \cbderivative{A}$.
-/
/-- The common derivative is closed and detects perfectness for closed sets. -/
theorem closed_relativeDerivative_spec [T1Space X] {A : Set X} (hA : IsClosed A) :
    relativeDerivative A = derivedSet A ∧ IsClosed (relativeDerivative A) ∧
      (Perfect A ↔ A = relativeDerivative A) := by
  rw [relativeDerivative_eq_derivedSet hA]
  exact ⟨rfl, isClosed_derivedSet A, perfect_iff_eq_derivedSet⟩

/-- The single recursion equation includes initial and limit stages. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Equivalently, all stages are given by the single recursion
    $$\cbderivative[\alpha]{F}
    = F\cap\bigcap_{\beta<\alpha}\cbderivative{(\cbderivative[\beta]{F})}.$$
-/
noncomputable def stage (F : Set X) (a : Ordinal.{u}) : Set X :=
  F ∩ {x | ∀ b < a, x ∈ derivedSet (stage F b)}
termination_by a

theorem stage_eq (F : Set X) (a : Ordinal.{u}) :
    stage F a = F ∩ {x | ∀ b < a, x ∈ derivedSet (stage F b)} := by
  rw [stage]

theorem stage_zero (F : Set X) : stage F 0 = F := by
  rw [stage_eq]
  simp

theorem stage_subset (F : Set X) (a : Ordinal.{u}) : stage F a ⊆ F := by
  rw [stage_eq]
  exact inter_subset_left

theorem stage_subset_derivative (F : Set X) {a b : Ordinal.{u}} (hab : a < b) :
    stage F b ⊆ derivedSet (stage F a) := by
  rw [stage_eq F b]
  exact fun _ hx => hx.2 a hab

theorem stage_closed [T1Space X] {F : Set X} (hF : IsClosed F) (a : Ordinal.{u}) :
    IsClosed (stage F a) := by
  rw [stage_eq]
  apply hF.inter
  have h := isClosed_iInter fun (b : Ordinal.{u}) =>
    isClosed_iInter fun (_ : b < a) => isClosed_derivedSet (stage F b)
  convert h using 1
  ext x
  simp

theorem stage_antitone [T1Space X] {F : Set X} (hF : IsClosed F) :
    Antitone (stage F) := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact Subset.rfl
  · exact (stage_subset_derivative F hab).trans
      ((isClosed_iff_derivedSet_subset _).mp (stage_closed hF a))

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    At a successor stage, the last derivative factor is contained in all the earlier factors.
    At a nonzero limit, every earlier stage has a later predecessor stage contained in its derivative.
    These observations give the successor and limit equations above and show that all stages are closed and decreasing.
-/
theorem stage_succ [T1Space X] {F : Set X} (hF : IsClosed F) (a : Ordinal.{u}) :
    stage F (a + 1) = derivedSet (stage F a) := by
  apply Subset.antisymm (stage_subset_derivative F (lt_add_one a))
  intro x hx
  rw [stage_eq]
  have hxa := (isClosed_iff_derivedSet_subset _).mp (stage_closed hF a) hx
  refine ⟨stage_subset F a hxa, fun b hb => ?_⟩
  exact derivedSet_mono _ _ (stage_antitone hF (lt_add_one_iff.mp hb)) hx

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Iterate by transfinite recursion on ordinals, using intersections at nonzero limit ordinals $\lambda$:
    $$\cbderivative[0]{F} = F, \qquad \cbderivative[\alpha+1]{F} = \cbderivative{(\cbderivative[\alpha]{F})}, \qquad
    \cbderivative[\lambda]{F} = \bigcap_{\beta < \lambda} \cbderivative[\beta]{F}.
-/
theorem stage_limit [T1Space X] {F : Set X} (hF : IsClosed F)
    {a : Ordinal.{u}} (ha : Order.IsSuccLimit a) :
    stage F a = ⋂ b < a, stage F b := by
  apply Subset.antisymm
  · exact fun x hx => mem_iInter₂.mpr fun b hb => stage_antitone hF hb.le hx
  · intro x hx
    have hx' := mem_iInter₂.mp hx
    rw [stage_eq]
    refine ⟨stage_subset F 0 (hx' 0 ha.bot_lt), fun b hb => ?_⟩
    exact stage_subset_derivative F (lt_add_one b) (hx' (b + 1) (ha.succ_lt hb))

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    \emph{Uniqueness.} The constructed $P$ is the largest perfect subset of $F$: if $Q \IncludedIn F$ is perfect, then $Q =
    \cbderivative{Q} \IncludedIn \cbderivative{F}$, and inductively $Q \IncludedIn \cbderivative[\alpha]{F}$ for every
    ordinal
    $\alpha$, so $Q \IncludedIn P$.
-/
theorem perfect_subset_stage {F P : Set X} (hP : Perfect P) (hPF : P ⊆ F)
    (a : Ordinal.{u}) : P ⊆ stage F a := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rw [stage_eq]
    intro x hx
    refine ⟨hPF hx, fun b hb => ?_⟩
    exact derivedSet_mono _ _ (ih b hb) ((perfect_iff_eq_derivedSet.mp hP) ▸ hx)

/-- Set-size bounds force a repeated stage, hence an adjacent equality. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    The chain must stabilize. Otherwise all stages would be distinct, contradicting the fact that the subsets of $F$
    form a set: take an ordinal whose cardinality exceeds that of the power set of $F$.
    If two stages coincide, the decreasing property forces the intervening successor stage to coincide as well.
-/
theorem exists_stable_stage [T1Space X] {F : Set X} (hF : IsClosed F) :
    ∃ a : Ordinal.{u}, stage F (a + 1) = stage F a := by
  have h := Cardinal.not_injective_limitation_set (stage F)
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h
  obtain ⟨a, b, heq, hne⟩ := h
  have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  have aux : ∀ a b : Ordinal.{u}, a < b → stage F a = stage F b →
      stage F (a + 1) = stage F a := by
    intro a b hab heq
    apply Subset.antisymm (stage_antitone hF (lt_add_one a).le)
    rw [heq]
    exact stage_antitone hF (add_one_le_of_lt hab)
  rcases lt_or_gt_of_ne hne' with hab | hba
  · exact ⟨a, aux a b hab heq⟩
  · exact ⟨b, aux b a hba heq.symm⟩

theorem stable_stage_perfect [T1Space X] {F : Set X} (hF : IsClosed F)
    {a : Ordinal.{u}} (ha : stage F (a + 1) = stage F a) : Perfect (stage F a) := by
  apply perfect_iff_eq_derivedSet.mpr
  exact ha.symm.trans (stage_succ hF a)

theorem stable_stage_later [T1Space X] {F : Set X} (hF : IsClosed F)
    {a b : Ordinal.{u}} (ha : stage F (a + 1) = stage F a) (hab : a ≤ b) :
    stage F b = stage F a :=
  (stage_antitone hF hab).antisymm
    (perfect_subset_stage (stable_stage_perfect hF ha) (stage_subset F a) b)

/-- Every lost point is removed at a successor step, including below limit stages. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    This ordinal is necessarily a successor — at a limit $\lambda$, every point surviving all earlier stages also lies in
    $\cbderivative[\lambda]{F} = \bigcap_{\beta < \lambda} \cbderivative[\beta]{F}$. So there is a unique $\phi(x)$ with
    $$x \in \SetDifference{\cbderivative[\phi(x)]{F}}{\cbderivative[\phi(x)+1]{F}},$$
-/
theorem exists_removal {F : Set X} {x : X} (hxF : x ∈ F) (a : Ordinal.{u})
    (hx : x ∉ stage F a) :
    ∃ b < a, x ∈ stage F b ∧ x ∉ derivedSet (stage F b) := by
  classical
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rw [stage_eq] at hx
    obtain ⟨b, hb, hxb⟩ : ∃ b < a, x ∉ derivedSet (stage F b) := by
      simp only [mem_inter_iff, mem_ofPred_eq, hxF, true_and] at hx
      push Not at hx
      exact hx
    by_cases hmem : x ∈ stage F b
    · exact ⟨b, hb, hmem, hxb⟩
    · obtain ⟨c, hc, hxc, hnot⟩ := ih b hb hmem
      exact ⟨c, hc.trans hb, hxc, hnot⟩

/-- A point cannot be removed at two different successor stages. -/
theorem removal_unique {F : Set X} {x : X} {a b : Ordinal.{u}}
    (ha : x ∈ stage F a) (ha' : x ∉ derivedSet (stage F a))
    (hb : x ∈ stage F b) (hb' : x ∉ derivedSet (stage F b)) : a = b := by
  rcases lt_trichotomy a b with hab | heq | hba
  · exact False.elim (ha' (stage_subset_derivative F hab hb))
  · exact heq
  · exact False.elim (hb' (stage_subset_derivative F hba ha))

/-- A basis element isolates a point that the derivative removes. -/
theorem exists_isolating_basic {B : Set (Set X)} (hB : IsTopologicalBasis B)
    {A : Set X} {x : X} (hx : x ∈ A) (hnot : x ∉ derivedSet A) :
    ∃ U ∈ B, x ∈ U ∧ U ∩ A = {x} := by
  classical
  rw [mem_derivedSet, accPt_iff_nhds] at hnot
  push Not at hnot
  obtain ⟨V, hV, hpoint⟩ := hnot
  obtain ⟨U, hUB, hxU, hUV⟩ := hB.mem_nhds_iff.mp hV
  refine ⟨U, hUB, hxU, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨hyU, hyA⟩
    exact hpoint y ⟨hUV hyU, hyA⟩
  · rintro y rfl
    exact ⟨hxU, hx⟩

/-- The basis code of a removed point is injective across all removal stages. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    The map $x \mapsto n(x)$ from $S$ to $\NN$ is injective: if $n(x) = n(y) = n$ with $\phi(x) \le \phi(y)$ (without loss
    of generality), then $y \in \cbderivative[\phi(y)]{F} \IncludedIn \cbderivative[\phi(x)]{F}$ and $y \in B_n$, so $y \in
    B_n \cap \cbderivative[\phi(x)]{F} = \{x\}$, forcing $y = x$. Hence $|S| \le \alephNull$.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    \emph{$S$ is countable.} Reusing the countable base $\{B_n\}$ above, observe that for each $x \in S$, since $x \in
    \cbderivative[0]{F}$ but $x \notin \cbderivative[\alpha_0]{F}$, there is a smallest ordinal at which $x$ is removed.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    meaning $x$ is isolated in $\cbderivative[\phi(x)]{F}$. Choose $n(x) \in \NN$ such that $B_{n(x)} \cap
    \cbderivative[\phi(x)]{F} = \{x\}$.
-/
theorem stage_complement_countable [T1Space X] [SecondCountableTopology X]
    {F : Set X} (hF : IsClosed F) (a : Ordinal.{u}) : (F \ stage F a).Countable := by
  classical
  obtain ⟨B, hBc, _, hB⟩ := TopologicalSpace.exists_countable_basis X
  have hdata : ∀ x : {x // x ∈ F \ stage F a}, ∃ b : Ordinal.{u},
      ∃ U : B, x.val ∈ stage F b ∧ x.val ∈ U.val ∧ U.val ∩ stage F b = {x.val} := by
    intro x
    obtain ⟨b, _, hxb, hxnot⟩ := exists_removal x.property.1 a x.property.2
    obtain ⟨U, hUB, hxU, hU⟩ := exists_isolating_basic hB hxb hxnot
    exact ⟨b, ⟨U, hUB⟩, hxb, hxU, hU⟩
  choose b U hmem hU hsingle using hdata
  have hinj : Function.Injective U := by
    intro x y hxy
    have aux : ∀ x y : {x // x ∈ F \ stage F a}, b x ≤ b y → U x = U y → y.val = x.val := by
      intro x y hle heq
      have hy : y.val ∈ (U x).val ∩ stage F (b x) :=
        ⟨heq ▸ hU y, stage_antitone hF hle (hmem y)⟩
      rwa [hsingle x, mem_singleton_iff] at hy
    rcases le_total (b x) (b y) with hle | hle
    · exact Subtype.ext (aux x y hle hxy).symm
    · exact Subtype.ext (aux y x hle hxy.symm)
  let : Countable B := hBc.to_subtype
  let := Function.Injective.countable hinj
  exact Set.to_countable _

/-- The decomposition uses the actual stable derivative stage. -/
theorem decomposition_exists [T1Space X] [SecondCountableTopology X]
    {F : Set X} (hF : IsClosed F) :
    ∃ a : Ordinal.{u}, Perfect (stage F a) ∧ (F \ stage F a).Countable ∧
      Disjoint (stage F a) (F \ stage F a) ∧ F = stage F a ∪ (F \ stage F a) := by
  obtain ⟨a, ha⟩ := exists_stable_stage hF
  refine ⟨a, stable_stage_perfect hF ha, stage_complement_countable hF a,
    disjoint_sdiff_right, ?_⟩
  exact (union_sdiff_cancel (stage_subset F a)).symm

/-- Each strict step before the first stable stage consumes a distinct basis element. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    The map $\alpha \mapsto n(\alpha)$ is injective
    on all $\alpha<\alpha_0$: if $n(\alpha) = n(\beta)$ with $\alpha < \beta$, then $B_{n(\beta)} \cap
    \cbderivative[\beta]{F} \IncludedIn B_{n(\alpha)} \cap \cbderivative[\alpha+1]{F} = \emptyset$, contradicting the choice
    at $\beta$.
-/
theorem strict_predecessors_countable [T1Space X] [SecondCountableTopology X]
    {F : Set X} (hF : IsClosed F) (a : Ordinal.{u})
    (hstrict : ∀ b < a, stage F (b + 1) ≠ stage F b) : (Iio a).Countable := by
  classical
  obtain ⟨B, hBc, _, hB⟩ := TopologicalSpace.exists_countable_basis X
  have hdata : ∀ b : Iio a, ∃ U : B,
      (U.val ∩ stage F b).Nonempty ∧ Disjoint U.val (stage F (b.val + 1)) := by
    intro b
    have hsub := stage_antitone hF (lt_add_one b.val).le
    obtain ⟨x, hxb, hxnot⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.mpr
      ⟨hsub, hstrict b b.property⟩)
    obtain ⟨U, hUB, hxU, hU⟩ := hB.exists_subset_of_mem_open hxnot
      (stage_closed hF (b.val + 1)).isOpen_compl
    refine ⟨⟨U, hUB⟩, ⟨x, hxU, hxb⟩, Set.disjoint_left.mpr ?_⟩
    exact fun y hy hyb => hU hy hyb
  choose U hmeet hmiss using hdata
  have hinj : Function.Injective U := by
    intro b c heq
    by_contra hne
    have hne' : b.val ≠ c.val := fun h => hne (Subtype.ext h)
    have aux : ∀ b c : Iio a, b.val < c.val → U b = U c → False := by
      intro b c hbc heq
      obtain ⟨x, hxU, hxc⟩ := hmeet c
      exact Set.disjoint_left.mp (hmiss b) (heq ▸ hxU)
        (stage_antitone hF (add_one_le_of_lt hbc) hxc)
    rcases lt_or_gt_of_ne hne' with hbc | hcb
    · exact aux b c hbc heq
    · exact aux c b hcb heq.symm
  let : Countable B := hBc.to_subtype
  let := hinj.countable
  exact Set.to_countable _

/-- The least stable stage is a countable ordinal, by the basis injection. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Thus $\alpha_0$ has only countably many predecessors, giving $\alpha_0 < \omegaOneOrd$.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    There is therefore
    a least ordinal $\alpha_0$ with $\cbderivative[\alpha_0+1]{F} = \cbderivative[\alpha_0]{F}$ — the
    \termdefineas{Cantor--Bendixson rank}{Cantor–Bendixson rank} of $F$. Second countability of $X$ forces $\alpha_0 <
    \omegaOneOrd$. Fix a countable base $\IndexedFamily{B_n}{n\in\NN}$ for the topology of $X$. At every $\alpha <
    \alpha_0$, the
    successor step is strict:
    $\cbderivative[\alpha+1]{F} \StrictlyIncludedIn \cbderivative[\alpha]{F}$. Choose a basic open $B_{n(\alpha)}$ that
    meets $\cbderivative[\alpha]{F}$ but not $\cbderivative[\alpha+1]{F}$.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Set
    $$P \;=\; \cbderivative[\alpha_0]{F}, \qquad S \;=\; \SetDifference{F}{P}.$$
    Then $P = \cbderivative{P}$, so $P$ is closed and has no isolated points — it is perfect (possibly empty).
-/
theorem exists_countable_rank [T1Space X] [SecondCountableTopology X]
    {F : Set X} (hF : IsClosed F) :
    ∃ a : Ordinal.{u}, a < Ordinal.omega 1 ∧ stage F (a + 1) = stage F a ∧
      ∀ b < a, stage F (b + 1) ≠ stage F b := by
  obtain ⟨a, ha, hleast⟩ := wellFounded_lt.has_min
    {a : Ordinal.{u} | stage F (a + 1) = stage F a} (exists_stable_stage hF)
  have hstrict : ∀ b < a, stage F (b + 1) ≠ stage F b :=
    fun b hb heq => hleast b heq hb
  refine ⟨a, ?_, ha, hstrict⟩
  have hcount := strict_predecessors_countable hF a hstrict
  have hcard := Cardinal.le_aleph0_iff_set_countable.mpr hcount
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0] at hcard
  exact Cardinal.lt_omega_iff_card_lt.mpr (Cardinal.lt_aleph_one_iff.mpr hcard)

end PolishSpaceBook.CantorBendixson
