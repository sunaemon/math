module

public import PolishSpaceBook.DomainScottTopology
public import Mathlib.Order.Interval.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! # Directed intersections in the real interval domain

NonemptyInterval has the inclusion order in mathlib. Taking its order dual and
adjoining a bottom gives exactly the book's information order. Nonemptiness of
directed intersections is proved by compactness, not assumed as extra data.
-/
namespace PolishSpaceBook
open Set Topology
set_option maxRecDepth 2048

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{IntervalDomain,IntervalBox}
    \end{mathmeta}
    The cleanest case study is the \termdefine{interval domain} $\IntervalDomain$:
    $$\IntervalDomain \;=\; \{[a, b] \IncludedIn \R : a \le b\} \cup \{\bot\}, \qquad
    [a, b] \sqsubseteq [c, d] \;\iff\; [c, d]
    \IncludedIn [a, b].$$
    Elements are nonempty closed bounded intervals ordered by *reverse inclusion*; the bottom element $\bot$ sits below
    every interval and represents "no information."
-/
abbrev IntervalInformation := WithBot (NonemptyInterval ℝ)ᵒᵈ

def intervalPoints : IntervalInformation → Set ℝ
  | ⊥ => univ
  | (I : (NonemptyInterval ℝ)ᵒᵈ) => ((OrderDual.ofDual I : NonemptyInterval ℝ) : Set ℝ)

@[simp] theorem intervalPoints_bot : intervalPoints ⊥ = univ := rfl
@[simp] theorem intervalPoints_coe (I : NonemptyInterval ℝ) :
    intervalPoints (↑(OrderDual.toDual I) : IntervalInformation) = (I : Set ℝ) := rfl

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{IntervalDomain,IntervalBox}
    \end{mathmeta}
    The cleanest case study is the \termdefine{interval domain} $\IntervalDomain$:
    $$\IntervalDomain \;=\; \{[a, b] \IncludedIn \R : a \le b\} \cup \{\bot\}, \qquad
    [a, b] \sqsubseteq [c, d] \;\iff\; [c, d]
    \IncludedIn [a, b].$$
    Elements are nonempty closed bounded intervals ordered by *reverse inclusion*; the bottom element $\bot$ sits below
    every interval and represents "no information."
-/
theorem interval_le_iff_points (I J : IntervalInformation) : I ≤ J ↔ intervalPoints J ⊆ intervalPoints I := by
  induction I using WithBot.recBotCoe with
  | bot => simp
  | coe I =>
    induction J using WithBot.recBotCoe with
    | bot =>
      constructor
      · intro h; exact False.elim (WithBot.not_coe_le_bot I h)
      · intro h
        have h' : (OrderDual.ofDual I).snd + 1 ≤ (OrderDual.ofDual I).snd :=
          (h (mem_univ _)).2
        linarith
    | coe J =>
      rw [WithBot.coe_le_coe]
      exact (NonemptyInterval.coe_subset_coe (s := OrderDual.ofDual J) (t := OrderDual.ofDual I)).symm

/-- The intersection of a nonempty directed family is itself a nonempty bounded interval. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    \begin{proof}
    Suppose $S$ contains an interval $I_0$. The interval members have the finite intersection property, since any finitely
    many have a common refinement in $S$, which is a nonempty interval. Intersecting each member with $I_0$ gives closed
    subsets of the compact interval $I_0$ with the finite intersection property. Hence the intersection $K$ of all interval
    members is nonempty. The set $K$ is compact and contains every point between any two of its points, so
    $K=[\min K,\max K]$. Reverse inclusion now makes $K$ the least upper bound of $S$.
    If $S$ contains no interval, nonemptiness gives $S=\{\bot\}$.
    Notice that a directed family need not be a nested sequence; the argument uses common refinements of finite
    subfamilies.
    \end{proof}
-/
theorem proper_interval_intersection (S : Set (NonemptyInterval ℝ)) (hne : S.Nonempty)
    (hd : DirectedOn (· ≥ ·) S) :
    ∃ I : NonemptyInterval ℝ, (I : Set ℝ) = ⋂ J ∈ S, (J : Set ℝ) := by
  let V : S → Set ℝ := fun J => (J.val : Set ℝ)
  have hdir : Directed (· ⊇ ·) V := by
    intro I J
    obtain ⟨K,hK,hKI,hKJ⟩ := hd I.val I.property J.val J.property
    exact ⟨⟨K,hK⟩,NonemptyInterval.coe_subset_coe.mpr hKI,NonemptyInterval.coe_subset_coe.mpr hKJ⟩
  let : Nonempty S := hne.to_subtype
  have hcompact (J : S) : IsCompact (V J) := isCompact_Icc
  have hclosed (J : S) : IsClosed (V J) := isClosed_Icc
  have hnonempty : (⋂ J, V J).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed V hdir
      (fun J => J.val.coe_nonempty) hcompact hclosed
  obtain ⟨J,hJ⟩ := hne
  have hc : IsCompact (⋂ J, V J) := (hcompact ⟨J,hJ⟩).of_isClosed_subset
    (isClosed_iInter hclosed) (iInter_subset V ⟨J,hJ⟩)
  obtain ⟨a,ha⟩ := hc.exists_isLeast hnonempty
  obtain ⟨b,hb⟩ := hc.exists_isGreatest hnonempty
  let I : NonemptyInterval ℝ := ⟨(a,b),hb.2 ha.1⟩
  refine ⟨I,?_⟩
  rw [biInter_eq_iInter]
  ext x
  constructor
  · intro hx
    apply mem_iInter.mpr
    intro J
    have haJ := mem_iInter.mp ha.1 J
    have hbJ := mem_iInter.mp hb.1 J
    exact ⟨haJ.1.trans hx.1,hx.2.trans hbJ.2⟩
  · intro hx
    exact ⟨ha.2 hx,hb.2 hx⟩

/-- A directed family of compact intervals eventually lies in any open set containing its intersection. -/
theorem proper_interval_eventually_subset (S : Set (NonemptyInterval ℝ)) (hne : S.Nonempty)
    (hd : DirectedOn (· ≥ ·) S) {U : Set ℝ} (hU : IsOpen U)
    (hsub : (⋂ J ∈ S, (J : Set ℝ)) ⊆ U) : ∃ J ∈ S, (J : Set ℝ) ⊆ U := by
  let : Nonempty S := hne.to_subtype
  have hdir : Directed (· ⊇ ·) (fun J : S => (J.val : Set ℝ)) := by
    intro I J
    obtain ⟨K,hK,hKI,hKJ⟩ := hd I.val I.property J.val J.property
    exact ⟨⟨K,hK⟩,NonemptyInterval.coe_subset_coe.mpr hKI,NonemptyInterval.coe_subset_coe.mpr hKJ⟩
  obtain ⟨J,hJ⟩ := exists_subset_nhds_of_isCompact' hdir (fun _ => isCompact_Icc)
    (fun _ => isClosed_Icc) (U := U) (mem_nhdsSet_iff_forall.mpr
      (fun x hx => hU.mem_nhds (hsub (mem_iInter₂.mpr (fun J hJ => mem_iInter.mp hx ⟨J,hJ⟩)))))
  exact ⟨J.val,J.property,hJ⟩

def properIntervals (S : Set IntervalInformation) : Set (NonemptyInterval ℝ) :=
  {I | (↑(OrderDual.toDual I) : IntervalInformation) ∈ S}

theorem properIntervals_directed {S : Set IntervalInformation} (hd : DirectedOn (· ≤ ·) S) :
    DirectedOn (· ≥ ·) (properIntervals S) := by
  intro I hI J hJ
  obtain ⟨K,hK,hIK,hJK⟩ := hd _ hI _ hJ
  induction K using WithBot.recBotCoe with
  | bot => exact False.elim (WithBot.not_coe_le_bot _ hIK)
  | coe K => exact ⟨OrderDual.ofDual K,hK,(WithBot.coe_le_coe (α := (NonemptyInterval ℝ)ᵒᵈ)).mp hIK,
      (WithBot.coe_le_coe (α := (NonemptyInterval ℝ)ᵒᵈ)).mp hJK⟩

theorem interval_isLUB_of_intersection {S : Set IntervalInformation} {I : NonemptyInterval ℝ}
    (hI : (I : Set ℝ) = ⋂ J ∈ properIntervals S, (J : Set ℝ)) :
    IsLUB S (↑(OrderDual.toDual I) : IntervalInformation) := by
  constructor
  · intro J hJ
    induction J using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe J =>
      apply (interval_le_iff_points _ _).mpr
      change (I : Set ℝ) ⊆ ((OrderDual.ofDual J : NonemptyInterval ℝ) : Set ℝ)
      rw [hI]
      exact iInter_subset_of_subset (OrderDual.ofDual J) (iInter_subset _ hJ)
  · intro J hJ
    apply (interval_le_iff_points _ _).mpr
    change intervalPoints J ⊆ (I : Set ℝ)
    rw [hI]
    intro x hx
    exact mem_iInter₂.mpr (fun K hK => (interval_le_iff_points _ _).mp (hJ hK) hx)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: proposition
  title: Directed completeness of the interval domain
-/
theorem interval_directed_has_lub (S : Set IntervalInformation) (hd : DirectedOn (· ≤ ·) S) :
    ∃ I, IsLUB S I := by
  classical
  by_cases hne : (properIntervals S).Nonempty
  · obtain ⟨I,hI⟩ := proper_interval_intersection (properIntervals S) hne (properIntervals_directed hd)
    exact ⟨↑(OrderDual.toDual I),interval_isLUB_of_intersection hI⟩
  · refine ⟨⊥,?_,fun _ _ => bot_le⟩
    intro J hJ
    induction J using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe J => exact False.elim (hne ⟨OrderDual.ofDual J,hJ⟩)

noncomputable instance intervalSupSet : SupSet IntervalInformation where
  sSup S := by
    classical
    exact if hd : DirectedOn (· ≤ ·) S then (interval_directed_has_lub S hd).choose else ⊥

noncomputable instance intervalCompletePartialOrder : CompletePartialOrder IntervalInformation where
  lubOfDirected S hd := by
    classical
    change IsLUB S (if h : DirectedOn (· ≤ ·) S then (interval_directed_has_lub S h).choose else ⊥)
    simpa only [dite_eq_left hd] using (interval_directed_has_lub S hd).choose_spec


theorem interval_points_of_lub {S : Set IntervalInformation} (hd : DirectedOn (· ≤ ·) S)
    (hne : (properIntervals S).Nonempty) {J : IntervalInformation} (hJ : IsLUB S J) :
    intervalPoints J = ⋂ I ∈ properIntervals S, (I : Set ℝ) := by
  obtain ⟨I,hI⟩ := proper_interval_intersection (properIntervals S) hne (properIntervals_directed hd)
  rw [hJ.unique (interval_isLUB_of_intersection hI),intervalPoints_coe,hI]

def intervalSingleton (x : ℝ) : IntervalInformation := ↑(OrderDual.toDual (NonemptyInterval.pure x))

@[simp] theorem intervalPoints_singleton (x : ℝ) : intervalPoints (intervalSingleton x) = {x} := by
  change Icc x x = {x}
  exact Icc_self x

theorem intervalPoints_nonempty (I : IntervalInformation) : (intervalPoints I).Nonempty := by
  induction I using WithBot.recBotCoe with
  | bot => exact univ_nonempty
  | coe I => exact (OrderDual.ofDual I).coe_nonempty

theorem intervalSingleton_isMax (x : ℝ) : IsMax (intervalSingleton x) := by
  intro J hJ
  apply (interval_le_iff_points _ _).mpr
  rw [intervalPoints_singleton]
  obtain ⟨y,hy⟩ := intervalPoints_nonempty J
  have he : y = x := by
    have h := (interval_le_iff_points _ _).mp hJ hy
    simpa only [intervalPoints_singleton,mem_singleton_iff] using h
  exact singleton_subset_iff.mpr (he ▸ hy)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Every interval is refined by the singleton interval of any of its points, and a singleton interval has no proper
    refinement. The bottom element is not maximal. This proves the assertion about maximal elements.
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    *   The maximal (= total) elements are precisely the singletons $\{x\} = [x, x]$, and identifying $[x, x]$ with $x$
        recovers $\R$ as a subspace of $\IntervalDomain$.
-/
theorem interval_isMax_iff (I : IntervalInformation) : IsMax I ↔ ∃ x, I = intervalSingleton x := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := intervalPoints_nonempty I
    have hle : I ≤ intervalSingleton x := by
      apply (interval_le_iff_points _ _).mpr
      simpa only [intervalPoints_singleton,singleton_subset_iff] using hx
    exact ⟨x,le_antisymm hle (h hle)⟩
  · rintro ⟨x,rfl⟩; exact intervalSingleton_isMax x

def intervalBox (U : Set ℝ) : Set IntervalInformation :=
  {I | I ≠ ⊥ ∧ intervalPoints I ⊆ U}

def surroundingIntervals (x : ℝ) : Set (NonemptyInterval ℝ) :=
  {I | I.fst < x ∧ x < I.snd}

theorem surroundingIntervals_nonempty (x : ℝ) : (surroundingIntervals x).Nonempty := by
  exact ⟨⟨(x-1,x+1),by linarith⟩,by dsimp [surroundingIntervals]; constructor <;> linarith⟩

theorem surroundingIntervals_directed (x : ℝ) : DirectedOn (· ≥ ·) (surroundingIntervals x) := by
  intro I hI J hJ
  have hl : max I.fst J.fst < x := max_lt hI.1 hJ.1
  have hr : x < min I.snd J.snd := lt_min hI.2 hJ.2
  refine ⟨⟨(max I.fst J.fst,min I.snd J.snd),hl.le.trans hr.le⟩,⟨hl,hr⟩,?_,?_⟩
  · exact ⟨le_max_left _ _,min_le_left _ _⟩
  · exact ⟨le_max_right _ _,min_le_right _ _⟩

theorem surroundingIntervals_intersection (x : ℝ) :
    (⋂ I ∈ surroundingIntervals x, (I : Set ℝ)) = {x} := by
  ext y
  constructor
  · intro hy
    apply mem_singleton_iff.mpr
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · let I : NonemptyInterval ℝ := ⟨((y+x)/2,x+1),by linarith⟩
      have hI : I ∈ surroundingIntervals x := by
        dsimp [surroundingIntervals,I]; constructor <;> linarith
      have hbound : (y+x)/2 ≤ y := (mem_iInter₂.mp hy I hI).1
      linarith
    · let I : NonemptyInterval ℝ := ⟨(x-1,(x+y)/2),by linarith⟩
      have hI : I ∈ surroundingIntervals x := by
        dsimp [surroundingIntervals,I]; constructor <;> linarith
      have hbound : y ≤ (x+y)/2 := (mem_iInter₂.mp hy I hI).2
      linarith
  · rintro rfl
    exact mem_iInter₂.mpr (fun I hI => ⟨hI.1.le,hI.2.le⟩)

def surroundingDomain (x : ℝ) : Set IntervalInformation :=
  (fun I : NonemptyInterval ℝ => (↑(OrderDual.toDual I) : IntervalInformation)) '' surroundingIntervals x

theorem properIntervals_surroundingDomain (x : ℝ) :
    properIntervals (surroundingDomain x) = surroundingIntervals x := by
  ext I
  simp [properIntervals,surroundingDomain]

theorem surroundingDomain_nonempty (x : ℝ) : (surroundingDomain x).Nonempty :=
  (surroundingIntervals_nonempty x).image _

theorem surroundingDomain_directed (x : ℝ) : DirectedOn (· ≤ ·) (surroundingDomain x) := by
  rintro _ ⟨I,hI,rfl⟩ _ ⟨J,hJ,rfl⟩
  obtain ⟨K,hK,hKI,hKJ⟩ := surroundingIntervals_directed x I hI J hJ
  exact ⟨↑(OrderDual.toDual K),⟨K,hK,rfl⟩,
    (WithBot.coe_le_coe (α := (NonemptyInterval ℝ)ᵒᵈ)).mpr hKI,
    (WithBot.coe_le_coe (α := (NonemptyInterval ℝ)ᵒᵈ)).mpr hKJ⟩

theorem surroundingDomain_isLUB (x : ℝ) : IsLUB (surroundingDomain x) (intervalSingleton x) := by
  apply interval_isLUB_of_intersection
  rw [properIntervals_surroundingDomain,surroundingIntervals_intersection]
  exact Icc_self x

section Scott
local instance intervalScottTopology : TopologicalSpace IntervalInformation := Topology.scott IntervalInformation univ
local instance intervalIsScott : Topology.IsScott IntervalInformation univ := ⟨rfl⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    For a rational open interval $(u,v)$, put
    $$\IntervalBox{u}{v}:=\{I\in\IntervalDomain:I\ne\bot,\ I\IncludedIn(u,v)\}.$$
    This is upward-closed. Suppose the intersection of the interval members of a directed family lies in $(u,v)$.
    If no member lies entirely in $(u,v)$, their intersections with the closed set $\SetDifference{\R}{(u,v)}$ have the finite
    intersection property. Compactness inside any fixed interval member then gives a point of their common
    intersection outside $(u,v)$, a contradiction. Thus $\IntervalBox{u}{v}$ is Scott-open. Its trace on singleton
    intervals is exactly $(u,v)$, so the relative Scott topology contains the usual topology of $\R$.
-/
theorem intervalBox_isOpen {U : Set ℝ} (hU : IsOpen U) : IsOpen (intervalBox U) := by
  apply (domain_scott_open_iff _).mpr
  constructor
  · intro I J hIJ hI
    exact ⟨fun hJ => hI.1 (le_bot_iff.mp (hJ ▸ hIJ)),
      ((interval_le_iff_points _ _).mp hIJ).trans hI.2⟩
  · intro S hne hd J hJ hJU
    have hproper : (properIntervals S).Nonempty := by
      by_contra hn
      apply hJU.1
      apply le_bot_iff.mp
      apply hJ.2
      intro I hI
      induction I using WithBot.recBotCoe with
      | bot => exact le_rfl
      | coe I => exact False.elim (hn ⟨OrderDual.ofDual I,hI⟩)
    have hsub : (⋂ I ∈ properIntervals S, (I : Set ℝ)) ⊆ U := by
      rw [← interval_points_of_lub hd hproper hJ]
      exact hJU.2
    obtain ⟨I,hI,hIU⟩ := proper_interval_eventually_subset (properIntervals S) hproper
      (properIntervals_directed hd) hU hsub
    exact ⟨↑(OrderDual.toDual I),hI,by simp,by simpa only [intervalPoints_coe] using hIU⟩

theorem intervalSingleton_preimage_box (U : Set ℝ) : intervalSingleton ⁻¹' intervalBox U = U := by
  ext x
  simp [intervalBox,intervalSingleton,singleton_subset_iff]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    For the other inclusion, let $V$ be Scott-open with $[x,x]\in V$. The family
    $$\{[a,b]:a<x<b\}$$
    is directed under reverse inclusion: intersect two such intervals to obtain a common refinement still containing
    $x$ in its interior. Its intersection is $\{x\}$, since every other point is excluded by some sufficiently small
    interval about $x$. Thus its supremum is $[x,x]$. Scott openness gives some $[a,b]\in V$ with $a<x<b$.
    For every $y\in(a,b)$, upward closure then gives $[y,y]\in V$. Hence the trace of $V$ on singleton intervals is
    open in the usual topology.
    \end{proof}
-/
theorem intervalSingleton_continuous : Continuous intervalSingleton := by
  apply continuous_def.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨hu,hi⟩ := (domain_scott_open_iff U).mp hU
  obtain ⟨J,hJ,hJU⟩ := hi (surroundingDomain_nonempty x) (surroundingDomain_directed x)
    (surroundingDomain_isLUB x) hx
  obtain ⟨I,hI,rfl⟩ := hJ
  apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hI)
  intro y hy
  apply hu _ hJU
  apply (interval_le_iff_points _ _).mpr
  simpa only [intervalPoints_singleton,intervalPoints_coe,singleton_subset_iff] using
    (show y ∈ (I : Set ℝ) from ⟨hy.1.le,hy.2.le⟩)

theorem intervalSingleton_isEmbedding : Topology.IsEmbedding intervalSingleton := by
  constructor
  · constructor
    apply TopologicalSpace.ext
    funext U
    apply propext
    rw [isOpen_induced_iff]
    constructor
    · intro hU
      exact ⟨intervalBox U,intervalBox_isOpen hU,intervalSingleton_preimage_box U⟩
    · rintro ⟨V,hV,rfl⟩
      exact hV.preimage intervalSingleton_continuous
  · intro x y h
    have he := congrArg intervalPoints h
    simpa only [intervalPoints_singleton,singleton_eq_singleton_iff] using he


theorem range_intervalSingleton : range intervalSingleton = {I | IsMax I} := by
  ext I
  simp only [mem_range, mem_ofPred_eq, interval_isMax_iff]
  exact exists_congr (fun x => eq_comm)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: proposition
  title: Topology on maximal intervals
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    *   The Scott topology, restricted to the maximal elements, is exactly the standard topology on $\R$.
-/
noncomputable def intervalMaximalHomeomorph : ℝ ≃ₜ {I : IntervalInformation // IsMax I} :=
  intervalSingleton_isEmbedding.toHomeomorph.trans (Homeomorph.setCongr range_intervalSingleton)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    *   The maximal (= total) elements are precisely the singletons $\{x\} = [x, x]$, and identifying $[x, x]$ with $x$
        recovers $\R$ as a subspace of $\IntervalDomain$.
-/
@[simp] theorem intervalMaximalHomeomorph_apply (x : ℝ) :
    (intervalMaximalHomeomorph x).val = intervalSingleton x := rfl

end Scott
end PolishSpaceBook
