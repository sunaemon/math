module

public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Part

@[expose] public section

/-! # Scott topology and finite information

The public statements use mathlib's Scott topology, Scott continuity, and
compact-element predicate. The way-below relation is given by existing directed
least upper bounds, so the general lemmas do not assume a bottom element.
-/
namespace PolishSpaceBook
open Set Topology

section Scott
variable {D E : Type*} [PartialOrder D] [PartialOrder E]
  [TopologicalSpace D] [TopologicalSpace E]
  [Topology.IsScott D univ] [Topology.IsScott E univ]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{Scott topology} declares $U \IncludedIn D$ open iff $U$ is upward-closed and inaccessible under directed
    suprema:
    $$
    \DirectedSup S \in U
    \;\Longrightarrow\;
    S \cap U \ne \emptyset
    \quad \text{for every directed } S \IncludedIn D.
    $$
    Equivalently, a Scott-open set is an observable property: once it holds of a completed value, it must already hold at
    some finite approximation.
-/
theorem domain_scott_open_iff (U : Set D) : IsOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by
  simpa only [dirSupInaccOn_univ] using
    (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (α := D) (D := univ) (s := U))

theorem domain_scott_principal_down_closed (a : D) : IsClosed (Iic a) := by
  apply Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed.mpr
  refine ⟨isLowerSet_Iic a,?_⟩
  intro S hS _ _ b hb
  exact hb.2 hS

/-- The order convention is `b ≤ a` iff `a` specializes to `b`. -/
theorem domain_scott_specializes_iff (a b : D) : a ⤳ b ↔ b ≤ a := by
  rw [specializes_iff_forall_open]
  constructor
  · intro h
    by_contra hb
    exact h (Iic a)ᶜ (domain_scott_principal_down_closed a).isOpen_compl hb le_rfl
  · intro h U hU hb
    exact ((domain_scott_open_iff U).mp hU).1 h hb

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Conversely, suppose $f$ is continuous for the Scott topologies. For any $a\in D$, the principal down-set
    $\mathord{\downarrow}a:=\{z\in D:z\sqsubseteq a\}$ is Scott-closed: it is downward-closed, and the supremum of a
    directed subset bounded above by $a$ is still below $a$. Consequently, with $U$ ranging over Scott-open sets,
    $$
    a\sqsubseteq b
    \quad\Longleftrightarrow\quad
    \forall U,\quad a\in U\Longrightarrow b\in U.
    $$
    The forward implication uses upward closure; for the converse, if $a\not\sqsubseteq b$, the complement of
    $\mathord{\downarrow}b$ is an open set containing $a$ but not $b$. Applying this characterization to inverse images
    of opens shows that $f$ is monotone.
-/
theorem domain_monotone_of_continuous {f : D → E} (hf : Continuous f) : Monotone f := by
  intro a b hab
  apply (domain_scott_specializes_iff (f b) (f a)).mp
  rw [specializes_iff_forall_open]
  intro U hU ha
  exact (specializes_iff_forall_open.mp ((domain_scott_specializes_iff b a).mpr hab))
    (f ⁻¹' U) (hU.preimage hf) ha

/-- The inverse-image proof follows the book, including the principal down-set argument. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: theorem
  title: Scott continuity and topological continuity
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Suppose $f:D\to E$ is monotone and preserves directed suprema. If $U\IncludedIn E$ is Scott-open, then
    $f^{-1}[U]$ is upward-closed. If $S\IncludedIn D$ is directed and $f(\DirectedSup S)\in U$, then
    $\DirectedSup f[S]\in U$. Since $f[S]$ is directed, some $s\in S$ satisfies $f(s)\in U$.
    Thus $f^{-1}[U]$ is Scott-open.
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Let $S\IncludedIn D$ be directed. Monotonicity makes $f(\DirectedSup S)$ an upper bound of $f[S]$.
    If $y\in E$ is any other upper bound, the closed set $f^{-1}[\mathord{\downarrow}y]$ contains $S$ and therefore
    contains $\DirectedSup S$. Hence $f(\DirectedSup S)\sqsubseteq y$. This proves that
    $f(\DirectedSup S)$ is the least upper bound of $f[S]$.
-/
theorem domain_scottContinuous_iff_continuous (f : D → E) :
    ScottContinuous f ↔ Continuous f := by
  constructor
  · intro hf
    have hm := hf.monotone
    apply continuous_def.mpr
    intro U hU
    obtain ⟨hu,hi⟩ := (domain_scott_open_iff U).mp hU
    apply (domain_scott_open_iff (f ⁻¹' U)).mpr
    refine ⟨fun a b hab ha => hu (hm hab) ha,?_⟩
    intro S hne hd s hs hfs
    have himage := directedOn_image.mpr (hd.mono hm)
    obtain ⟨y,⟨x,hx,rfl⟩,hy⟩ := hi (hne.image f) himage (hf hne hd hs) hfs
    exact ⟨x,hx,hy⟩
  · intro hf
    have hm := domain_monotone_of_continuous hf
    intro S hne hd s hs
    refine ⟨?_,?_⟩
    · rintro _ ⟨x,hx,rfl⟩; exact hm (hs.1 hx)
    · intro y hy
      have hclosed : IsClosed (f ⁻¹' Iic y) := (domain_scott_principal_down_closed y).preimage hf
      have hsubset : S ⊆ f ⁻¹' Iic y := fun x hx => hy ⟨x,hx,rfl⟩
      exact (Topology.IsScott.dirSupClosed_of_isClosed hclosed) hsubset hne hd hs

/-- Every open neighborhood of the least element is the whole domain. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Scott topologies are $T_0$. For a nontrivial dcpo with a least element, $\bot$ lies in the closure of every nonempty
    subset. Such a space is not $T_1$, and hence is not Hausdorff.
-/
theorem domain_bot_mem_closure [OrderBot D] {S : Set D} (hS : S.Nonempty) : (⊥ : D) ∈ closure S := by
  obtain ⟨a,ha⟩ := hS
  have hs : a ⤳ (⊥ : D) := (domain_scott_specializes_iff a ⊥).mpr bot_le
  exact closure_mono (singleton_subset_iff.mpr ha) (specializes_iff_mem_closure.mp hs)

end Scott

/-- Approximation tested against all nonempty directed families with a least upper bound. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    A dcpo usually carries a least element $\bot$, representing "no information," "undefined," or "non-terminating." The
    \termdefine{way-below relation} formalizes finite approximation:
    $$
    a\ll b
    \quad\Longleftrightarrow\quad
    \text{for every directed }S,\; b\sqsubseteq\DirectedSup S
    \text{ implies }(\exists s\in S)\; a\sqsubseteq s.
    $$
    Thus $a\ll b$ means that whenever a directed computation eventually reaches enough information to cover $b$, it must
    already reach enough information to cover $a$ at some finite stage.
-/
def DomainWayBelow {D : Type*} [Preorder D] (a b : D) : Prop :=
  ∀ (S : Set D) (s : D), S.Nonempty → DirectedOn (· ≤ ·) S → IsLUB S s →
    b ≤ s → ∃ x ∈ S, a ≤ x

theorem domainWayBelow_le {D : Type*} [Preorder D] {a b : D} (h : DomainWayBelow a b) : a ≤ b := by
  obtain ⟨x,hx,hax⟩ := h {b} b (singleton_nonempty b) (directedOn_singleton b) (isLUB_singleton (a := b)) le_rfl
  simpa only [mem_singleton_iff.mp hx] using hax

theorem domainWayBelow_self_iff_compact {D : Type*} [PartialOrder D] (a : D) :
    DomainWayBelow a a ↔ IsCompactElement a := Iff.rfl

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The bottom element is way below every element because a directed set is nonempty and all its members lie above
    $\bot$. Also, $I\ll\bot$ implies $I\sqsubseteq\bot$ by applying the definition to the singleton directed set
    $\{\bot\}$, so $I=\bot$.
-/
/-- The bottom element requires no positive information. -/
theorem domainWayBelow_bot {D : Type*} [PartialOrder D] [OrderBot D] (b : D) :
    DomainWayBelow ⊥ b := by
  intro S s hne _ _ _
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,hx,bot_le⟩

theorem domainWayBelow_bot_iff {D : Type*} [PartialOrder D] [OrderBot D] (a : D) :
    DomainWayBelow a ⊥ ↔ a = ⊥ := by
  constructor
  · intro h; exact le_bot_iff.mp (domainWayBelow_le h)
  · rintro rfl; exact domainWayBelow_bot ⊥

/-- The book's basis condition, stated with least upper bounds rather than a chosen supremum. -/
def IsDomainBasis {D : Type*} [PartialOrder D] (B : Set D) : Prop :=
  ∀ x, (B ∩ {a | DomainWayBelow a x}).Nonempty ∧
    DirectedOn (· ≤ ·) (B ∩ {a | DomainWayBelow a x}) ∧
    IsLUB (B ∩ {a | DomainWayBelow a x}) x

/-- A basis also gives the full continuous-domain condition. -/
theorem IsDomainBasis.continuous {D : Type*} [PartialOrder D] {B : Set D} (hB : IsDomainBasis B) (x : D) :
    {a | DomainWayBelow a x}.Nonempty ∧ DirectedOn (· ≤ ·) {a | DomainWayBelow a x} ∧
      IsLUB {a | DomainWayBelow a x} x := by
  obtain ⟨hne,hd,hlub⟩ := hB x
  refine ⟨hne.mono inter_subset_right,?_,?_,?_⟩
  · intro a ha b hb
    obtain ⟨c,hc,hac⟩ := ha _ _ hne hd hlub le_rfl
    obtain ⟨d,hdd,hbd⟩ := hb _ _ hne hd hlub le_rfl
    obtain ⟨e,he,hce,hde⟩ := hd c hc d hdd
    exact ⟨e,he.2,hac.trans hce,hbd.trans hde⟩
  · intro a ha
    exact domainWayBelow_le ha
  · intro y hy
    exact hlub.2 (fun a ha => hy ha.2)

/-- A finite amount of positive information occurs together in one directed stage. -/
theorem finite_subset_directed_union {α : Type*} {F : Set α} (hF : F.Finite)
    {S : Set (Set α)} (hne : S.Nonempty) (hd : DirectedOn (· ⊆ ·) S)
    (hsub : F ⊆ ⋃₀ S) : ∃ A ∈ S, F ⊆ A := by
  induction F,hF using Set.Finite.induction_on with
  | empty => obtain ⟨A,hA⟩ := hne; exact ⟨A,hA,empty_subset A⟩
  | @insert x F hx hfin ih =>
    obtain ⟨A,hA,hxA⟩ := hsub (mem_insert x F)
    obtain ⟨B,hB,hFB⟩ := ih (fun z hz => hsub (mem_insert_of_mem _ hz))
    obtain ⟨C,hC,hAC,hBC⟩ := hd A hA B hB
    exact ⟨C,hC,insert_subset_iff.mpr ⟨hAC hxA,fun z hz => hBC (hFB hz)⟩⟩

theorem finite_wayBelow_powerset_iff {α : Type*} {F A : Set α} (hF : F.Finite) :
    DomainWayBelow F A ↔ F ⊆ A := by
  refine ⟨domainWayBelow_le,fun hFA S s hne hd hs hAs => ?_⟩
  have he : s = ⋃₀ S := hs.unique (isLUB_sSup S)
  exact finite_subset_directed_union hF hne hd (he ▸ hFA.trans hAs)

def finiteApproximants {α : Type*} (A : Set α) : Set (Set α) := {F | F.Finite ∧ F ⊆ A}

theorem finiteApproximants_nonempty {α : Type*} (A : Set α) : (finiteApproximants A).Nonempty :=
  ⟨∅,finite_empty,empty_subset A⟩

theorem finiteApproximants_directed {α : Type*} (A : Set α) :
    DirectedOn (· ≤ ·) (finiteApproximants A) := by
  intro F hF G hG
  exact ⟨F ∪ G,⟨hF.1.union hG.1,union_subset hF.2 hG.2⟩,subset_union_left,subset_union_right⟩

theorem finiteApproximants_isLUB {α : Type*} (A : Set α) : IsLUB (finiteApproximants A) A := by
  refine ⟨fun _ hF => hF.2,fun B hB x hx => ?_⟩
  exact hB ⟨finite_singleton x,singleton_subset_iff.mpr hx⟩ (mem_singleton x)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Scott topology on Pomega{Scott topology on $omega$}
-/
theorem wayBelow_powerset_iff {α : Type*} (F A : Set α) :
    DomainWayBelow F A ↔ F.Finite ∧ F ⊆ A := by
  constructor
  · intro h
    obtain ⟨G,hG,hFG⟩ := h (finiteApproximants A) A (finiteApproximants_nonempty A)
      (finiteApproximants_directed A) (finiteApproximants_isLUB A) le_rfl
    exact ⟨hG.1.subset hFG,domainWayBelow_le h⟩
  · rintro ⟨hF,hFA⟩
    exact (finite_wayBelow_powerset_iff hF).mpr hFA

theorem countable_finite_natural_sets : {F : Set ℕ | F.Finite}.Countable :=
  Set.Countable.ofPred_finite

section Powerset
variable {α : Type*}
local instance powersetScottTopology : TopologicalSpace (Set α) := Topology.scott (Set α) univ
local instance powersetIsScott : Topology.IsScott (Set α) univ := ⟨rfl⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Scott topology on Pomega{Scott topology on $omega$}
-/
theorem powerset_scott_open_iff (U : Set (Set α)) :
    IsOpen U ↔ ∀ A ∈ U, ∃ F : Set α, F.Finite ∧ F ⊆ A ∧ Ici F ⊆ U := by
  constructor
  · intro hU A hA
    obtain ⟨hu,hi⟩ := (domain_scott_open_iff U).mp hU
    obtain ⟨F,hF,hFU⟩ := hi (finiteApproximants_nonempty A) (finiteApproximants_directed A)
      (finiteApproximants_isLUB A) hA
    exact ⟨F,hF.1,hF.2,fun B hFB => hu hFB hFU⟩
  · intro h
    apply (domain_scott_open_iff U).mpr
    refine ⟨?_,?_⟩
    · intro A B hAB hA
      obtain ⟨F,_,hFA,hFU⟩ := h A hA
      exact hFU (hFA.trans hAB)
    · intro S hne hd A hA hAU
      obtain ⟨F,hF,hFA,hFU⟩ := h A hAU
      obtain ⟨B,hB,hFB⟩ := (finite_wayBelow_powerset_iff hF).mpr hFA S A hne hd hA le_rfl
      exact ⟨B,hB,hFU hFB⟩

theorem powerset_principal_finite_isOpen {F : Set α} (hF : F.Finite) : IsOpen (Ici F) := by
  apply (powerset_scott_open_iff _).mpr
  intro A hA
  exact ⟨F,hF,hA,subset_rfl⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    $\PowerSet{\omega}$ need not be $T_1$.
-/
theorem powerset_scott_not_t1 [Nonempty α] : ¬ T1Space (Set α) := by
  intro hT
  let := hT
  obtain ⟨x⟩ := ‹Nonempty α›
  have h : ({x} : Set α) ⤳ ∅ := (domain_scott_specializes_iff _ _).mpr (empty_subset _)
  have he := specializes_iff_eq.mp h
  exact Set.singleton_ne_empty x he

end Powerset
section Flat
variable {α : Type*}
local instance flatScottTopology : TopologicalSpace (Part α) := Topology.scott (Part α) univ
local instance flatIsScott : Topology.IsScott (Part α) univ := ⟨rfl⟩

theorem flat_some_le_iff (a : α) (b : Part α) : Part.some a ≤ b ↔ b = Part.some a := by
  constructor
  · intro h; exact Part.eq_some_iff.mpr (h a (Part.mem_some a))
  · rintro rfl; exact le_rfl

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The flat domain $\FlatNaturals := \NN \cup \{\bot\}$ has order
    $\bot \sqsubseteq n$ for every $n \in \NN$, with distinct natural numbers incomparable.
    Every directed subset has a greatest element. Indeed, if it contains $n\in\NN$, a common upper bound of $n$ and
    any other member must be $n$ itself. Otherwise its only member is $\bot$.
    Thus the flat domain is a dcpo, and every upward-closed set is Scott-open: a directed supremum already belongs to
    the directed set. Its Scott-open sets are exactly the subsets of $\NN$ together with $\FlatNaturals$ itself.
    Observing membership in a nontrivial Scott-open set therefore means seeing a completed numerical value; no finite
    observation distinguishes nontermination $\bot$ from a computation that has merely not halted yet.
-/
theorem flat_directed_has_greatest {S : Set (Part α)} (hne : S.Nonempty)
    (hd : DirectedOn (· ≤ ·) S) : ∃ a, IsGreatest S a := by
  classical
  by_cases hs : ∃ a, Part.some a ∈ S
  · obtain ⟨a,ha⟩ := hs
    refine ⟨Part.some a,ha,fun b hb => ?_⟩
    obtain ⟨c,hc,hac,hbc⟩ := hd _ ha _ hb
    exact (flat_some_le_iff a c).mp hac ▸ hbc
  · have hn : ∀ b ∈ S, b = Part.none := by
      intro b hb
      rcases Part.eq_none_or_eq_some b with h | ⟨a,rfl⟩
      · exact h
      · exact False.elim (hs ⟨a,hb⟩)
    obtain ⟨b,hb⟩ := hne
    exact ⟨Part.none,hn b hb ▸ hb,fun c hc => by rw [hn c hc]⟩

theorem flat_directed_has_lub {S : Set (Part α)} (hne : S.Nonempty)
    (hd : DirectedOn (· ≤ ·) S) : ∃ a, IsLUB S a := by
  obtain ⟨a,ha⟩ := flat_directed_has_greatest hne hd
  exact ⟨a,ha.isLUB⟩

theorem flat_scott_open_iff (U : Set (Part α)) :
    IsOpen U ↔ (Part.none ∈ U → U = univ) := by
  constructor
  · intro hU hb
    apply eq_univ_of_forall
    intro a
    exact ((domain_scott_open_iff U).mp hU).1 (bot_le : (⊥ : Part α) ≤ a) hb
  · intro hU
    apply (domain_scott_open_iff U).mpr
    refine ⟨?_,?_⟩
    · intro a b hab ha
      rcases Part.eq_none_or_eq_some a with rfl | ⟨n,rfl⟩
      · rw [hU ha]; trivial
      · exact (flat_some_le_iff n b).mp hab ▸ ha
    · intro S hne hd a ha haU
      obtain ⟨b,hb⟩ := flat_directed_has_greatest hne hd
      exact ⟨b,hb.1,ha.unique hb.isLUB ▸ haU⟩

end Flat
end PolishSpaceBook
