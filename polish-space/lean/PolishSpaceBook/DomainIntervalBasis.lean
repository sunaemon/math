module

public import PolishSpaceBook.DomainIntervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Rat.Encodable

@[expose] public section

/-! # Finite interval information and a rational basis

Strict containment in the interior characterizes approximation in the interval
domain. Rational enlargements provide the directed families used both to prove
necessity and to obtain a countable basis.
-/
namespace PolishSpaceBook
open Set Topology

local instance intervalBasisScottTopology : TopologicalSpace IntervalInformation :=
  Topology.scott IntervalInformation univ
local instance intervalBasisIsScott : Topology.IsScott IntervalInformation univ := ⟨rfl⟩

/-- Regard a closed real interval as an element of the information order. -/
def intervalElement (I : NonemptyInterval ℝ) : IntervalInformation := ↑(OrderDual.toDual I)

@[simp] theorem intervalElement_le (I J : NonemptyInterval ℝ) :
    intervalElement I ≤ intervalElement J ↔ I.fst ≤ J.fst ∧ J.snd ≤ I.snd := by
  exact WithBot.coe_le_coe

@[simp] theorem intervalElement_ne_bot (I : NonemptyInterval ℝ) : intervalElement I ≠ ⊥ := by
  exact WithBot.coe_ne_bot

@[simp] theorem intervalPoints_element (I : NonemptyInterval ℝ) : intervalPoints (intervalElement I) = (I : Set ℝ) := rfl

/-- A rational interval, viewed as a real interval. -/
def realRationalInterval (I : NonemptyInterval ℚ) : NonemptyInterval ℝ :=
  ⟨((I.fst : ℝ),(I.snd : ℝ)),by change (I.fst : ℝ) ≤ (I.snd : ℝ); exact_mod_cast I.fst_le_snd⟩

def rationalEnlargements (J : NonemptyInterval ℝ) : Set (NonemptyInterval ℚ) :=
  {I | (I.fst : ℝ) < J.fst ∧ J.snd < (I.snd : ℝ)}

theorem rationalEnlargements_nonempty (J : NonemptyInterval ℝ) : (rationalEnlargements J).Nonempty := by
  obtain ⟨a,ha⟩ := exists_rat_lt J.fst
  obtain ⟨b,hb⟩ := exists_rat_gt J.snd
  have hab : a ≤ b := by exact_mod_cast (ha.le.trans (J.fst_le_snd.trans hb.le))
  exact ⟨⟨(a,b),hab⟩,ha,hb⟩

theorem rationalEnlargements_directed (J : NonemptyInterval ℝ) :
    DirectedOn (· ≥ ·) (rationalEnlargements J) := by
  intro I hI K hK
  have hl : (max I.fst K.fst : ℚ) < J.fst := by
    simpa only [Rat.cast_max] using max_lt hI.1 hK.1
  have hr : J.snd < (min I.snd K.snd : ℚ) := by
    simpa only [Rat.cast_min] using lt_min hI.2 hK.2
  have hlr : max I.fst K.fst ≤ min I.snd K.snd := by
    exact_mod_cast (hl.le.trans (J.fst_le_snd.trans hr.le))
  exact ⟨⟨(max I.fst K.fst,min I.snd K.snd),hlr⟩,⟨hl,hr⟩,
    ⟨le_max_left _ _,min_le_left _ _⟩,⟨le_max_right _ _,min_le_right _ _⟩⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    \begin{proof}
    Fix $J=[c,d]$ and consider its rational enlargements
    $$
    R_J:=\{[u,v]:u,v\in\QQ,\ u<c,\ d<v\}.
    $$
    This family is nonempty by density of $\QQ$ in $\R$. It is directed under reverse inclusion: the intersection of two
    members has rational endpoints and still contains $J$ in its interior. Its intersection is exactly $J$.
    Indeed, a point smaller than $c$ can be excluded by choosing a rational left endpoint between that point and $c$;
    a point larger than $d$ can be excluded similarly on the right. Hence $\DirectedSup R_J=J$.
-/
theorem rationalEnlargements_intersection (J : NonemptyInterval ℝ) :
    (⋂ I ∈ rationalEnlargements J, (realRationalInterval I : Set ℝ)) = (J : Set ℝ) := by
  ext x
  constructor
  · intro hx
    constructor
    · by_contra h
      obtain ⟨a,ha⟩ := exists_rat_btwn (lt_of_not_ge h)
      obtain ⟨b,hb⟩ := exists_rat_gt J.snd
      have hab : a ≤ b := by exact_mod_cast (ha.2.le.trans (J.fst_le_snd.trans hb.le))
      let I : NonemptyInterval ℚ := ⟨(a,b),hab⟩
      have hI : I ∈ rationalEnlargements J := ⟨ha.2,hb⟩
      have hax : (a : ℝ) ≤ x := (mem_iInter₂.mp hx I hI).1
      exact (not_le_of_gt ha.1) hax
    · by_contra h
      obtain ⟨b,hb⟩ := exists_rat_btwn (lt_of_not_ge h)
      obtain ⟨a,ha⟩ := exists_rat_lt J.fst
      have hab : a ≤ b := by exact_mod_cast (ha.le.trans (J.fst_le_snd.trans hb.1.le))
      let I : NonemptyInterval ℚ := ⟨(a,b),hab⟩
      have hI : I ∈ rationalEnlargements J := ⟨ha,hb.1⟩
      have hxb : x ≤ (b : ℝ) := (mem_iInter₂.mp hx I hI).2
      exact (not_le_of_gt hb.2) hxb
  · intro hx
    exact mem_iInter₂.mpr (fun I hI => ⟨hI.1.le.trans hx.1,hx.2.trans hI.2.le⟩)

def rationalApproximationFamily (J : NonemptyInterval ℝ) : Set IntervalInformation :=
  (intervalElement ∘ realRationalInterval) '' rationalEnlargements J

theorem rationalApproximationFamily_nonempty (J : NonemptyInterval ℝ) :
    (rationalApproximationFamily J).Nonempty := (rationalEnlargements_nonempty J).image _

theorem rationalApproximationFamily_directed (J : NonemptyInterval ℝ) :
    DirectedOn (· ≤ ·) (rationalApproximationFamily J) := by
  rintro _ ⟨I,hI,rfl⟩ _ ⟨K,hK,rfl⟩
  obtain ⟨L,hL,hLI,hLK⟩ := rationalEnlargements_directed J I hI K hK
  refine ⟨_,⟨L,hL,rfl⟩,?_,?_⟩
  · apply (intervalElement_le _ _).mpr
    exact ⟨by exact Rat.cast_le.mpr hLI.1,by exact Rat.cast_le.mpr hLI.2⟩
  · apply (intervalElement_le _ _).mpr
    exact ⟨by exact Rat.cast_le.mpr hLK.1,by exact Rat.cast_le.mpr hLK.2⟩

theorem rationalApproximationFamily_isLUB (J : NonemptyInterval ℝ) :
    IsLUB (rationalApproximationFamily J) (intervalElement J) := by
  constructor
  · rintro _ ⟨I,hI,rfl⟩
    exact (intervalElement_le _ _).mpr ⟨hI.1.le,hI.2.le⟩
  · intro K hK
    apply (interval_le_iff_points _ _).mpr
    rw [intervalPoints_element,← rationalEnlargements_intersection J]
    intro x hx
    exact mem_iInter₂.mpr (fun I hI => (interval_le_iff_points _ _).mp (hK ⟨I,hI,rfl⟩) hx)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: proposition
  title: Approximation and a rational basis
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    If $[a,b]\ll J$, applying the definition to $R_J$ gives $[u,v]\in R_J$ with
    $[a,b]\sqsubseteq[u,v]$. Therefore $a\le u<c$ and $d<v\le b$, proving the strict inequalities.
    Conversely, suppose $a<c$ and $d<b$, and let $S$ be directed with $J\sqsubseteq\DirectedSup S$.
    The intersection of the interval members of $S$ is contained in $J$, hence in $(a,b)$.
    The compactness argument in the preceding proof gives some interval member $K\IncludedIn(a,b)$.
    Then $[a,b]\sqsubseteq K$, as required.
-/
theorem interval_wayBelow_iff (I J : NonemptyInterval ℝ) :
    DomainWayBelow (intervalElement I) (intervalElement J) ↔ I.fst < J.fst ∧ J.snd < I.snd := by
  constructor
  · intro h
    obtain ⟨K,⟨R,hR,rfl⟩,hIK⟩ := h _ _ (rationalApproximationFamily_nonempty J)
      (rationalApproximationFamily_directed J) (rationalApproximationFamily_isLUB J) le_rfl
    have hIR := (intervalElement_le _ _).mp hIK
    exact ⟨hIR.1.trans_lt hR.1,hR.2.trans_le hIR.2⟩
  · rintro ⟨hl,hr⟩ S L hne hd hL hJL
    have hproper : L ≠ ⊥ := fun h => intervalElement_ne_bot J (le_bot_iff.mp (h ▸ hJL))
    have hbox : L ∈ intervalBox (Ioo I.fst I.snd) := by
      refine ⟨hproper,?_⟩
      intro x hx
      have hxJ : x ∈ (J : Set ℝ) := (interval_le_iff_points _ _).mp hJL hx
      exact ⟨hl.trans_le hxJ.1,hxJ.2.trans_lt hr⟩
    obtain ⟨K,hK,hKI⟩ := ((domain_scott_open_iff _).mp (intervalBox_isOpen isOpen_Ioo)).2 hne hd hL hbox
    refine ⟨K,hK,(interval_le_iff_points _ _).mpr ?_⟩
    intro x hx
    exact ⟨(hKI.2 hx).1.le,(hKI.2 hx).2.le⟩

/-- The bottom element together with all intervals having rational endpoints. -/
def rationalIntervalBasis : Set IntervalInformation :=
  insert ⊥ (range (intervalElement ∘ realRationalInterval))

theorem rationalIntervalBasis_countable : rationalIntervalBasis.Countable := by
  let : Countable (NonemptyInterval ℚ) := NonemptyInterval.toProd_injective.countable
  exact (countable_range _).insert ⊥

theorem rationalIntervalBasis_approximants (J : NonemptyInterval ℝ) :
    rationalIntervalBasis ∩ {I | DomainWayBelow I (intervalElement J)} =
      insert ⊥ (rationalApproximationFamily J) := by
  ext I
  constructor
  · rintro ⟨hI,hw⟩
    rcases hI with rfl | ⟨R,rfl⟩
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨R,(interval_wayBelow_iff _ _).mp hw,rfl⟩
  · rintro (rfl | ⟨R,hR,rfl⟩)
    · exact ⟨mem_insert _ _,domainWayBelow_bot _⟩
    · exact ⟨mem_insert_of_mem _ ⟨R,rfl⟩,(interval_wayBelow_iff _ _).mpr hR⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The set $B$ is countable because $\QQ^2$ is countable. For an interval element $J$, the characterization just proved
    gives
    $$
    \{I\in B:I\ll J\}=\{\bot\}\cup R_J.
    $$
    This set is directed with supremum $J$. For the bottom element, the corresponding set is just $\{\bot\}$.
    These are precisely the basis conditions. They also give continuity: every element way below $J$ lies below some
    member of the directed basis family, by the definition of way-below. Thus any two such approximants have a common
    upper bound in that family. All approximants are below $J$, and they include the basis family with supremum $J$,
    so their supremum is $J$ as well.
-/
theorem rationalIntervalBasis_isBasis : IsDomainBasis rationalIntervalBasis := by
  intro I
  induction I using WithBot.recBotCoe with
  | bot =>
    have he : rationalIntervalBasis ∩ {I | DomainWayBelow I ⊥} = {⊥} := by
      ext I
      simp only [mem_inter_iff,mem_ofPred_eq,domainWayBelow_bot_iff,mem_singleton_iff]
      constructor
      · exact And.right
      · rintro rfl; exact ⟨mem_insert _ _,rfl⟩
    rw [he]
    exact ⟨singleton_nonempty _,directedOn_singleton _,isLUB_singleton⟩
  | coe J =>
    change (rationalIntervalBasis ∩ {I | DomainWayBelow I (intervalElement (OrderDual.ofDual J))}).Nonempty ∧
      DirectedOn (· ≤ ·) (rationalIntervalBasis ∩ {I | DomainWayBelow I (intervalElement (OrderDual.ofDual J))}) ∧
      IsLUB (rationalIntervalBasis ∩ {I | DomainWayBelow I (intervalElement (OrderDual.ofDual J))}) (intervalElement (OrderDual.ofDual J))
    rw [rationalIntervalBasis_approximants]
    refine ⟨⟨⊥,mem_insert _ _⟩,?_,?_,?_⟩
    · intro a ha b hb
      rcases ha with rfl | ha
      · exact ⟨b,hb,bot_le,le_rfl⟩
      rcases hb with rfl | hb
      · exact ⟨a,mem_insert_of_mem _ ha,le_rfl,bot_le⟩
      obtain ⟨c,hc,hac,hbc⟩ := rationalApproximationFamily_directed (OrderDual.ofDual J) a ha b hb
      exact ⟨c,mem_insert_of_mem _ hc,hac,hbc⟩
    · intro a ha
      rcases ha with rfl | ha
      · exact bot_le
      · exact (rationalApproximationFamily_isLUB (OrderDual.ofDual J)).1 ha
    · intro b hb
      exact (rationalApproximationFamily_isLUB (OrderDual.ofDual J)).2 (fun a ha => hb (mem_insert_of_mem _ ha))

/-- The explicit countable basis and hence continuity of the interval domain. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: proposition
  title: Approximation and a rational basis
-/
theorem interval_countable_basis : rationalIntervalBasis.Countable ∧ IsDomainBasis rationalIntervalBasis :=
  ⟨rationalIntervalBasis_countable,rationalIntervalBasis_isBasis⟩

theorem interval_domain_continuous (I : IntervalInformation) :
    {J | DomainWayBelow J I}.Nonempty ∧ DirectedOn (· ≤ ·) {J | DomainWayBelow J I} ∧
      IsLUB {J | DomainWayBelow J I} I := rationalIntervalBasis_isBasis.continuous I

/-- Approximation can be interpolated through a rational basis element. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: corollary
  title: Interpolation through rational intervals
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    If $I=\bot$, take $K=\bot$. Otherwise write $I=[a,b]$ and $J=[c,d]$; the bottom case for $J$ is impossible.
    Choose rational numbers $u,v$ with
    $$
    a<u<c\le d<v<b.
    $$
    Then $K=[u,v]$ has the required properties by the strict endpoint characterization.
-/
theorem interval_wayBelow_basis_interpolation {I J : IntervalInformation} (h : DomainWayBelow I J) :
    ∃ K ∈ rationalIntervalBasis, DomainWayBelow I K ∧ DomainWayBelow K J := by
  induction I using WithBot.recBotCoe with
  | bot => exact ⟨⊥,mem_insert _ _,domainWayBelow_bot _,domainWayBelow_bot _⟩
  | coe I =>
    induction J using WithBot.recBotCoe with
    | bot => exact False.elim (WithBot.coe_ne_bot ((domainWayBelow_bot_iff _).mp h))
    | coe J =>
      have hIJ := (interval_wayBelow_iff (OrderDual.ofDual I) (OrderDual.ofDual J)).mp h
      obtain ⟨a,ha⟩ := exists_rat_btwn hIJ.1
      obtain ⟨b,hb⟩ := exists_rat_btwn hIJ.2
      have hab : a ≤ b := by
        exact_mod_cast (ha.2.le.trans ((OrderDual.ofDual J).fst_le_snd.trans hb.1.le))
      let R : NonemptyInterval ℚ := ⟨(a,b),hab⟩
      refine ⟨intervalElement (realRationalInterval R),mem_insert_of_mem _ ⟨R,rfl⟩,?_,?_⟩
      · exact (interval_wayBelow_iff _ _).mpr ⟨ha.1,hb.2⟩
      · exact (interval_wayBelow_iff _ _).mpr ⟨ha.2,hb.1⟩

end PolishSpaceBook
