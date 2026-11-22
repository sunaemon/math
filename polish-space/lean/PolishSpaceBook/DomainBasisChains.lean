module

public import PolishSpaceBook.DomainScottTopology
public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-! # Interpolation and basis chains

The interpolation argument flattens two successive levels of basis approximation.
It then constructs cofinal chains by repeatedly interpolating a common upper
approximation. All choices here are topological, with no effectiveness claim.
-/
namespace PolishSpaceBook
open Set Topology
section Order
variable {D : Type*} [PartialOrder D]

theorem DomainWayBelow.mono {a b c d : D} (h : DomainWayBelow b c) (hab : a ≤ b) (hcd : c ≤ d) :
    DomainWayBelow a d := by
  intro S s hne hd hs hds
  obtain ⟨x,hx,hbx⟩ := h S s hne hd hs (hcd.trans hds)
  exact ⟨x,hx,hab.trans hbx⟩

def basisApproximants (B : Set D) (x : D) : Set D := B ∩ {a | DomainWayBelow a x}

def secondBasisApproximants (B : Set D) (x : D) : Set D :=
  {a | a ∈ B ∧ ∃ b ∈ B, DomainWayBelow a b ∧ DomainWayBelow b x}

variable {B : Set D}

theorem secondBasisApproximants_nonempty (hB : IsDomainBasis B) (x : D) :
    (secondBasisApproximants B x).Nonempty := by
  obtain ⟨b,hb⟩ := (hB x).1
  obtain ⟨a,ha⟩ := (hB b).1
  exact ⟨a,ha.1,b,hb.1,ha.2,hb.2⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The definition of way-below directly gives the implication
    $$a\sqsubseteq u\ll v\sqsubseteq x\quad\Longrightarrow\quad a\ll x.$$
    Write
    $$B_x:=\{b\in B:b\ll x\},\qquad T_x:=\bigcup_{b\in B_x}B_b.$$
    The set $T_x$ is nonempty, since every set of basis approximants is nonempty. It is also directed.
    Indeed, take $u\in B_b$ and $v\in B_c$ with $b,c\in B_x$, and choose a common upper bound $e\in B_x$ of $b,c$.
    Then $u\ll e$ and $v\ll e$. Applying these two relations to the directed family $B_e$ gives members of $B_e$
    above $u$ and $v$, respectively. A common upper bound of those members in $B_e$ belongs to $T_x$ and is above both
    $u$ and $v$.
-/
theorem secondBasisApproximants_directed (hB : IsDomainBasis B) (x : D) :
    DirectedOn (· ≤ ·) (secondBasisApproximants B x) := by
  rintro a ⟨ha,b,hb,hab,hbx⟩ c ⟨hc,d,hdd,hcd,hdx⟩
  obtain ⟨e,he,hbe,hde⟩ := (hB x).2.1 b ⟨hb,hbx⟩ d ⟨hdd,hdx⟩
  have hae := hab.mono le_rfl hbe
  have hce := hcd.mono le_rfl hde
  obtain ⟨u,hu,hau⟩ := hae _ _ (hB e).1 (hB e).2.1 (hB e).2.2 le_rfl
  obtain ⟨v,hv,hcv⟩ := hce _ _ (hB e).1 (hB e).2.1 (hB e).2.2 le_rfl
  obtain ⟨w,hw,huw,hvw⟩ := (hB e).2.1 u hu v hv
  exact ⟨w,⟨hw.1,e,he.1,hw.2,he.2⟩,hau.trans huw,hcv.trans hvw⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Every member of $T_x$ is below $x$. Conversely, an upper bound $y$ of $T_x$ bounds every $B_b$ for $b\in B_x$,
    so it bounds each $b=\DirectedSup B_b$ and then $x=\DirectedSup B_x$. Thus $\DirectedSup T_x=x$.
    Apply $a\ll x$ to this directed family. There are $u\in B_b$ and $b\in B_x$ with $a\sqsubseteq u$.
    It follows that $a\ll b\ll x$, proving interpolation through the chosen basis.
-/
theorem secondBasisApproximants_isLUB (hB : IsDomainBasis B) (x : D) :
    IsLUB (secondBasisApproximants B x) x := by
  constructor
  · rintro a ⟨_,b,_,hab,hbx⟩
    exact (domainWayBelow_le hab).trans (domainWayBelow_le hbx)
  · intro y hy
    apply (hB x).2.2.2
    intro b hb
    apply (hB b).2.2.2
    intro a ha
    exact hy ⟨ha.1,b,hb.1,ha.2,hb.2⟩

/-- Interpolation through an element of the chosen basis. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: lemma
  title: Interpolation through a domain basis
-/
theorem IsDomainBasis.interpolate (hB : IsDomainBasis B) {a x : D} (hax : DomainWayBelow a x) :
    ∃ b ∈ B, DomainWayBelow a b ∧ DomainWayBelow b x := by
  obtain ⟨u,⟨_,b,hb,hub,hbx⟩,hau⟩ := hax _ _ (secondBasisApproximants_nonempty hB x)
    (secondBasisApproximants_directed hB x) (secondBasisApproximants_isLUB hB x) le_rfl
  exact ⟨b,hb,hub.mono hau le_rfl,hbx⟩

/-- Extend a previous approximation while also covering a new one. -/
theorem IsDomainBasis.next_approximation (hB : IsDomainBasis B) {x a r : D}
    (ha : a ∈ basisApproximants B x) (hr : r ∈ basisApproximants B x) :
    ∃ b ∈ basisApproximants B x, DomainWayBelow a b ∧ r ≤ b := by
  obtain ⟨u,hu,hau,hru⟩ := (hB x).2.1 a ha r hr
  obtain ⟨b,hb,hub,hbx⟩ := hB.interpolate hu.2
  exact ⟨b,⟨hb,hbx⟩,hub.mono hau le_rfl,hru.trans (domainWayBelow_le hub)⟩

noncomputable def nextBasisApproximation (hB : IsDomainBasis B) {x : D}
    (a r : basisApproximants B x) : basisApproximants B x :=
  ⟨(hB.next_approximation a.property r.property).choose,
    (hB.next_approximation a.property r.property).choose_spec.1⟩

theorem nextBasisApproximation_spec (hB : IsDomainBasis B) {x : D} (a r : basisApproximants B x) :
    DomainWayBelow a.val (nextBasisApproximation hB a r).val ∧ r.val ≤ (nextBasisApproximation hB a r).val :=
  (hB.next_approximation a.property r.property).choose_spec.2

noncomputable def cofinalBasisChain (hB : IsDomainBasis B) {x : D}
    (r : ℕ → basisApproximants B x) : ℕ → basisApproximants B x
  | 0 => r 0
  | n+1 => nextBasisApproximation hB (cofinalBasisChain hB r n) (r (n+1))

theorem cofinalBasisChain_step (hB : IsDomainBasis B) {x : D} (r : ℕ → basisApproximants B x) (n : ℕ) :
    DomainWayBelow (cofinalBasisChain hB r n).val (cofinalBasisChain hB r (n+1)).val :=
  (nextBasisApproximation_spec hB _ _).1

theorem cofinalBasisChain_covers (hB : IsDomainBasis B) {x : D} (r : ℕ → basisApproximants B x) (n : ℕ) :
    (r n).val ≤ (cofinalBasisChain hB r n).val := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact (nextBasisApproximation_spec hB _ _).2

/-- A countable basis yields a cofinal way-below-increasing sequence below every point. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: lemma
  title: Cofinal basis chains
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Enumerate the nonempty countable set $B_x$ as a sequence $\Sequence{r_n}{n\in\omega}$, allowing repetitions, and set
    $c_0=r_0$.
    Given $c_n$, choose $u_n\in B_x$ above both $c_n$ and $r_{n+1}$. The
    \termuseas{domain interpolation lemma}{interpolation lemma} gives $c_{n+1}\in B$ with
    $$u_n\ll c_{n+1}\ll x.$$
    Then $c_n\ll c_{n+1}$ and $r_{n+1}\sqsubseteq c_{n+1}$. Inductively, the chain is increasing and each term
    dominates all earlier enumerated approximants. Every member of $B_x$ is therefore below some $c_n$.
    All $c_n$ are below $x$, and any upper bound of the chain bounds $B_x$, whose supremum is $x$.
    Hence $\DirectedSup_n c_n=x$.
-/
theorem IsDomainBasis.exists_cofinal_chain (hB : IsDomainBasis B) (hcount : B.Countable) (x : D) :
    ∃ c : ℕ → D, (∀ n, c n ∈ basisApproximants B x) ∧
      (∀ n, DomainWayBelow (c n) (c (n+1))) ∧
      (∀ a ∈ basisApproximants B x, ∃ n, a ≤ c n) ∧ IsLUB (range c) x := by
  have hAcount : (basisApproximants B x).Countable := hcount.mono inter_subset_left
  obtain ⟨r,hr⟩ := hAcount.exists_surjective (hB x).1
  let c : ℕ → D := fun n => (cofinalBasisChain hB r n).val
  have hcofinal : ∀ a ∈ basisApproximants B x, ∃ n, a ≤ c n := by
    intro a ha
    obtain ⟨n,hn⟩ := hr ⟨a,ha⟩
    refine ⟨n,?_⟩
    have he : (r n).val = a := congrArg Subtype.val hn
    rw [← he]
    exact cofinalBasisChain_covers hB r n
  refine ⟨c,fun n => (cofinalBasisChain hB r n).property,cofinalBasisChain_step hB r,hcofinal,?_,?_⟩
  · rintro _ ⟨n,rfl⟩
    exact domainWayBelow_le (cofinalBasisChain hB r n).property.2
  · intro y hy
    apply (hB x).2.2.2
    intro a ha
    obtain ⟨n,hn⟩ := hcofinal a ha
    exact hn.trans (hy ⟨n,rfl⟩)

section Scott
variable [TopologicalSpace D] [Topology.IsScott D univ]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    For any $a\in D$, the set $W_a$ is upward-closed. If $a\ll\DirectedSup S$, interpolate to obtain
    $a\ll b\ll\DirectedSup S$. Some $d\in S$ satisfies $b\sqsubseteq d$, whence $a\ll d$.
    Thus $W_a$ is Scott-open. Finally, let $U$ be Scott-open with $x\in U$. Since $\DirectedSup B_x=x$, some
    $b\in B_x$ belongs to $U$. Upward closure gives
    $$x\in W_b\IncludedIn U,$$
    which proves the basis assertion.
-/
theorem IsDomainBasis.wayBelow_isOpen (hB : IsDomainBasis B) (a : D) :
    IsOpen {x | DomainWayBelow a x} := by
  apply (domain_scott_open_iff _).mpr
  constructor
  · intro x y hxy hx
    exact hx.mono le_rfl hxy
  · intro S hne hd x hx hax
    obtain ⟨b,_,hab,hbx⟩ := hB.interpolate hax
    obtain ⟨s,hs,hbs⟩ := hbx S x hne hd hx le_rfl
    exact ⟨s,hs,hab.mono le_rfl hbs⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: lemma
  title: Interpolation through a domain basis
-/
theorem IsDomainBasis.scott_open_iff (hB : IsDomainBasis B) (U : Set D) :
    IsOpen U ↔ ∀ x ∈ U, ∃ b ∈ B, DomainWayBelow b x ∧ {y | DomainWayBelow b y} ⊆ U := by
  constructor
  · intro hU x hx
    obtain ⟨hu,hi⟩ := (domain_scott_open_iff U).mp hU
    obtain ⟨b,hb,hbU⟩ := hi (hB x).1 (hB x).2.1 (hB x).2.2 hx
    exact ⟨b,hb.1,hb.2,fun y hy => hu (domainWayBelow_le hy) hbU⟩
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨b,hb,hbx,hbU⟩ := h x hx
    exact Filter.mem_of_superset ((hB.wayBelow_isOpen b).mem_nhds hbx) hbU

end Scott
end Order

section Names
variable {D : Type*} [OmegaCompletePartialOrder D]
open OmegaCompletePartialOrder

/-- Names satisfying the way-below chain condition. -/
def basisChainNames (b : ℕ → D) : Set (ℕ → ℕ) :=
  {p | ∀ n, DomainWayBelow (b (p n)) (b (p (n+1)))}

def basisNameChain (b : ℕ → D) (p : basisChainNames b) : Chain D where
  toFun n := b (p.val n)
  monotone' := monotone_nat_of_le_succ (fun n => domainWayBelow_le (p.property n))

def basisNameSup (b : ℕ → D) (p : basisChainNames b) : D := ωSup (basisNameChain b p)

theorem basisNameSup_isLUB (b : ℕ → D) (p : basisChainNames b) :
    IsLUB (range (fun n => b (p.val n))) (basisNameSup b p) :=
  isLUB_range_ωSup (basisNameChain b p)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The chain condition is closed, since a failure is witnessed by two adjacent coordinates. On this closed space of
    names, the supremum map into $D$ is continuous for the Scott topology. Indeed, for any Scott-open set $U$,
    $$
    \DirectedSup_n b_{p(n)}\in U\quad\Longleftrightarrow\quad
    \exists n\; b_{p(n)}\in U.
    $$
    The forward implication is inaccessibility, and the reverse implication is upward closure. Each condition on the right
    depends on a single coordinate of the name, so its truth is determined by a finite prefix.
-/
theorem basisChainNames_isClosed (b : ℕ → D) : IsClosed (basisChainNames b) := by
  have he : basisChainNames b = ⋂ n, {p : ℕ → ℕ | DomainWayBelow (b (p n)) (b (p (n+1)))} := by
    ext p
    simp [basisChainNames]
  rw [he]
  apply isClosed_iInter
  intro n
  have hc : Continuous (fun p : ℕ → ℕ => (p n,p (n+1))) :=
    (continuous_apply n).prodMk (continuous_apply (n+1))
  exact (isClosed_discrete (s := {q : ℕ × ℕ | DomainWayBelow (b q.1) (b q.2)})).preimage hc

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    For surjectivity, fix $x\in X$ and apply the \termuse{cofinal basis chain lemma} to the chosen countable basis.
    It gives $c_n\ll c_{n+1}\ll x$ with $\DirectedSup_n c_n=x$. Choose indices $p(n)$ so that $b_{p(n)}=c_n$.
    Then $p$ is a name and $\DomainRepresentation{X}(p)=x$.
-/
theorem basisNameSup_surjective (b : ℕ → D) (hB : IsDomainBasis (range b)) :
    Function.Surjective (basisNameSup b) := by
  classical
  intro x
  obtain ⟨c,hc,hstep,_,hlub⟩ := hB.exists_cofinal_chain (countable_range b) x
  let p : ℕ → ℕ := fun n => (hc n).1.choose
  have hcodes (n : ℕ) : b (p n) = c n := (hc n).1.choose_spec
  have hp : p ∈ basisChainNames b := by
    intro n
    rw [hcodes,hcodes]
    exact hstep n
  refine ⟨⟨p,hp⟩,?_⟩
  apply (basisNameSup_isLUB b ⟨p,hp⟩).unique
  have he : (fun n => b (p n)) = c := funext hcodes
  simpa only [he] using hlub

section Scott
variable [TopologicalSpace D] [Topology.IsScott D univ]

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The chain condition is closed, since a failure is witnessed by two adjacent coordinates. On this closed space of
    names, the supremum map into $D$ is continuous for the Scott topology. Indeed, for any Scott-open set $U$,
    $$
    \DirectedSup_n b_{p(n)}\in U\quad\Longleftrightarrow\quad
    \exists n\; b_{p(n)}\in U.
    $$
    The forward implication is inaccessibility, and the reverse implication is upward closure. Each condition on the right
    depends on a single coordinate of the name, so its truth is determined by a finite prefix.
-/
theorem basisNameSup_continuous (b : ℕ → D) : Continuous (basisNameSup b) := by
  apply continuous_def.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨hu,hi⟩ := (domain_scott_open_iff U).mp hU
  obtain ⟨a,⟨n,rfl⟩,ha⟩ := hi (range_nonempty (basisNameChain b p))
    (basisNameChain b p).directed.directedOn_range (basisNameSup_isLUB b p) hp
  have hc : Continuous (fun q : basisChainNames b => q.val n) :=
    (continuous_apply n).comp continuous_subtype_val
  have ho : IsOpen {q : basisChainNames b | q.val n = p.val n} :=
    (isOpen_discrete (s := {p.val n})).preimage hc
  apply Filter.mem_of_superset (ho.mem_nhds rfl)
  intro q hq
  apply hu (le_ωSup (basisNameChain b q) n)
  change b (q.val n) ∈ U
  change q.val n = p.val n at hq
  rw [hq]
  exact ha

end Scott
end Names
end PolishSpaceBook
