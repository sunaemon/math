module

public import PolishSpaceBook.DomainTheoryQuasiPolishSpaces

@[expose] public section

/-! # Admissibility of domain-chain representations

Open sets are tested through a fixed enumeration of subordinate cylinders.
Finite stages absorb all certificates seen so far. Disjointifying subordinate
cylinders makes each selected basis index locally constant. These are classical
topological choices; no effective enumeration of the auxiliary data is assumed.
-/

namespace PolishSpaceBook
open Set Topology Function

/-- A countable open cover of a subspace of Baire space admits a continuous
choice of a covering index. The proof enumerates subordinate cylinders and
chooses the first one containing the input. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: lemma
  title: Continuous choice from an open cover
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    If $E$ is empty, use the empty map. Otherwise enumerate all pairs $\Pair{s_i}{k_i}$ such that
    $$V_i:=E\cap\cyl{s_i}\IncludedIn U_{k_i}.$$
    These relative cylinders cover $E$, since cylinders form a basis of Baire space. They are relatively clopen.
    For each $q\in E$, let $\iota(q)$ be the least index with $q\in V_{\iota(q)}$, and put $h(q)=k_{\iota(q)}$.
    The nonempty sets
    $$C_i:=\SetDifference{V_i}{\bigcup_{j<i}V_j}$$
    form a relatively clopen partition of $E$. On each $C_i$, the chosen index is constantly $i$ and $h$ is constantly
    $k_i$. Thus $h$ is continuous and makes the required choice.
-/
theorem exists_continuous_open_choice {E : Set baire_space} (U : ℕ → Set E)
    (hU : ∀ n, IsOpen (U n)) (hcover : ∀ p, ∃ n, p ∈ U n) :
    ∃ h : E → ℕ, Continuous h ∧ ∀ p, p ∈ U (h p) := by
  classical
  by_cases hE : Nonempty E
  · let := hE
    let Good := {v : finseq ℕ × ℕ // ∀ p : E, p.val ∈ cyl v.1 → p ∈ U v.2}
    have cover (p : E) : ∃ v : Good, p.val ∈ cyl v.val.1 := by
      obtain ⟨i,hi⟩ := hcover p
      obtain ⟨O,hO,hOU⟩ := isOpen_induced_iff.mp (hU i)
      have hpO : p.val ∈ O := by change p ∈ Subtype.val ⁻¹' O; rw [hOU]; exact hi
      obtain ⟨s,hps,hsO⟩ := exists_cyl_subset_of_mem_open hpO hO
      refine ⟨⟨(s,i),?_⟩,hps⟩
      intro z hz
      rw [← hOU]
      exact hsO hz
    obtain ⟨v,_⟩ := cover (Classical.arbitrary E)
    let : Nonempty Good := ⟨v⟩
    obtain ⟨e,he⟩ := exists_surjective_nat Good
    let A : ℕ → Set E := fun n => Subtype.val ⁻¹' cyl (e n).val.1
    have hA (n) : IsClopen (A n) :=
      (baire_cyl_clopen (e n).val.1).preimage continuous_subtype_val
    have hc (p : E) : ∃ n, p ∈ A n := by
      obtain ⟨v,hv⟩ := cover p
      obtain ⟨n,rfl⟩ := he v
      exact ⟨n,hv⟩
    let pick : E → ℕ := fun p => Nat.find (hc p)
    have hpick (p : E) : p ∈ disjointSeq A (pick p) := by
      refine ⟨Nat.find_spec (hc p),?_⟩
      intro hp
      obtain ⟨k,hp⟩ := mem_iUnion.mp hp
      obtain ⟨hk,hp⟩ := mem_iUnion.mp hp
      exact Nat.find_min (hc p) (Finset.mem_range.mp hk) hp
    have hconstant {p z : E} (hz : z ∈ disjointSeq A (pick p)) : pick z = pick p := by
      by_contra hne
      exact Set.disjoint_left.mp (disjointSeq_pairwiseDisjoint A hne) (hpick z) hz
    let h : E → ℕ := fun p => (e (pick p)).val.2
    refine ⟨h,?_,fun p => (e (pick p)).property p (hpick p).1⟩
    apply continuous_def.mpr
    intro V _
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    apply Filter.mem_of_superset ((disjointSeq_isClopen hA (pick p)).isOpen.mem_nhds (hpick p))
    intro z hz
    change h z ∈ V
    simpa only [h,hconstant hz,mem_preimage] using hp
  · let : IsEmpty E := not_nonempty_iff.mp hE
    exact ⟨fun p => isEmptyElim p,continuous_iff_continuousAt.mpr (fun p => isEmptyElim p),
      fun p => isEmptyElim p⟩

section Basis
variable {D : Type*} [PartialOrder D] {B : Set D}

/-- Directedness combines a previous approximant with finitely many certificates. -/
theorem IsDomainBasis.finite_bound (hB : IsDomainBasis B) {x a : D}
    (ha : a ∈ basisApproximants B x) (r : ℕ → D) (s : Finset ℕ)
    (hr : ∀ i ∈ s, r i ∈ basisApproximants B x) :
    ∃ u ∈ basisApproximants B x, a ≤ u ∧ ∀ i ∈ s, r i ≤ u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨a,ha,le_rfl,by simp⟩
  | @insert i s his ih =>
    obtain ⟨v,hv,hav,hsv⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    obtain ⟨u,hu,hvu,hru⟩ := (hB x).2.1 v hv (r i) (hr i (Finset.mem_insert_self _ _))
    refine ⟨u,hu,hav.trans hvu,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hru
    · exact (hsv j hj).trans hvu

variable [TopologicalSpace D] [Topology.IsScott D univ]
variable (b : ℕ → D) {E : Set baire_space} (g : E → D)

/-- A finite-input certificate that a particular basis element approximates the value. -/
def DomainCertificate :=
  {v : finseq ℕ × ℕ // ∀ p : E, p.val ∈ cyl v.1 → DomainWayBelow (b v.2) (g p)}

def certificateSet (v : DomainCertificate b g) : Set E := Subtype.val ⁻¹' cyl v.val.1

omit [TopologicalSpace D] [Topology.IsScott D univ] in
theorem certificateSet_isClopen (v : DomainCertificate b g) : IsClopen (certificateSet b g v) :=
  (baire_cyl_clopen v.val.1).preimage continuous_subtype_val

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The continuity and surjectivity arguments above apply to any subspace; the additional complexity assertion was also
    proved above. We establish the universal property from §{sec:cauchy-representation-admissibility}.
    Let $\delta:E\to X$ be any continuous partial map with $E\IncludedIn\BaireSpace$.
    For empty $E$ the translator is the empty map, so assume $E$ is nonempty. Write
    $$W_{b_j}=\{x\in D:b_j\ll x\}.$$
    These sets are Scott-open by the \termuse{domain interpolation lemma}. Fix an enumeration of all pairs
    $\Pair{s_i}{k_i}$ satisfying
    $$V_i:=E\cap\cyl{s_i}\IncludedIn\delta^{-1}[W_{b_{k_i}}].$$
    Each $V_i$ is relatively clopen. Moreover, whenever $b_k\ll\delta(q)$, relative openness gives a cylinder certificate
    with $q\in V_i$ and $k_i=k$.
-/
theorem exists_domainCertificate (hB : IsDomainBasis (range b)) (hg : Continuous g)
    (p : E) (i : ℕ) (hi : DomainWayBelow (b i) (g p)) :
    ∃ v : DomainCertificate b g, v.val.2 = i ∧ p ∈ certificateSet b g v := by
  have ho : IsOpen (g ⁻¹' {x | DomainWayBelow (b i) x}) :=
    (hB.wayBelow_isOpen (b i)).preimage hg
  obtain ⟨O,hO,hOU⟩ := isOpen_induced_iff.mp ho
  have hpO : p.val ∈ O := by change p ∈ Subtype.val ⁻¹' O; rw [hOU]; exact hi
  obtain ⟨s,hps,hsO⟩ := exists_cyl_subset_of_mem_open hpO hO
  refine ⟨⟨(s,i),?_⟩,rfl,hps⟩
  intro z hz
  have : z ∈ Subtype.val ⁻¹' O := hsO hz
  rw [hOU] at this
  exact this

/-- A continuously chosen basis approximation to each represented value. -/
def DomainApproximation := {h : E → ℕ // Continuous h ∧ ∀ p, DomainWayBelow (b (h p)) (g p)}

theorem exists_domainApproximation (hB : IsDomainBasis (range b)) (hg : Continuous g) :
    Nonempty (DomainApproximation b g) := by
  have hc (p : E) : ∃ i, DomainWayBelow (b i) (g p) := by
    obtain ⟨a,⟨i,rfl⟩,ha⟩ := (hB (g p)).1
    exact ⟨i,ha⟩
  obtain ⟨h,hh,hspec⟩ := exists_continuous_open_choice
    (fun i => g ⁻¹' {x | DomainWayBelow (b i) x})
    (fun i => (hB.wayBelow_isOpen (b i)).preimage hg) hc
  exact ⟨⟨h,hh,hspec⟩⟩

/-- The candidate index must refine the preceding choice and absorb every
applicable certificate among the first `n` entries. -/
def nextDomainCandidate (e : ℕ → DomainCertificate b g) (n : ℕ)
    (h : DomainApproximation b g) (j : ℕ) : Set E :=
  {p | DomainWayBelow (b j) (g p) ∧ DomainWayBelow (b (h.val p)) (b j) ∧
    ∀ i < n, p ∈ certificateSet b g (e i) → b (e i).val.2 ≤ b j}

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    We recursively construct continuous maps $h_n:E\to\omega$. The relatively open sets
    $\delta^{-1}[W_{b_j}]$ cover $E$, since the basis approximants below each point are nonempty.
    The \termuse{continuous choice from an open cover} therefore gives $h_0$ with
    $$b_{h_0(q)}\ll\delta(q).$$
    Suppose $h_n$ has been chosen with $b_{h_n(q)}\ll\delta(q)$ for all $q$. For each $j$, let $U_j^n$ consist of the
    points $q\in E$ satisfying
    $$
    \begin{aligned}
    b_j&\ll\delta(q),\qquad b_{h_n(q)}\ll b_j,\\
    \forall i\le n\;&\bigl(q\in V_i\Longrightarrow b_{k_i}\sqsubseteq b_j\bigr).
    \end{aligned}
    $$
    These sets are relatively open. The first condition is open by continuity of $\delta$; the second is locally constant
    because $h_n$ is continuous into the discrete space $\omega$. Each of the finitely many remaining conditions is either
    vacuous or the relatively clopen condition $q\notin V_i$.
-/
theorem nextDomainCandidate_isOpen (hB : IsDomainBasis (range b)) (hg : Continuous g)
    (e : ℕ → DomainCertificate b g) (n : ℕ) (h : DomainApproximation b g) (j : ℕ) :
    IsOpen (nextDomainCandidate b g e n h j) := by
  have he : nextDomainCandidate b g e n h j =
      (g ⁻¹' {x | DomainWayBelow (b j) x}) ∩
      (h.val ⁻¹' {i | DomainWayBelow (b i) (b j)}) ∩
      ⋂ i : Fin n, {p | p ∈ certificateSet b g (e i) → b (e i).val.2 ≤ b j} := by
    ext p
    simp [nextDomainCandidate,and_assoc,Fin.forall_iff]
  rw [he]
  apply IsOpen.inter
  · exact ((hB.wayBelow_isOpen (b j)).preimage hg).inter
      ((isOpen_discrete _).preimage h.property.1)
  · apply isOpen_iInter_of_finite
    intro i
    by_cases hi : b (e i).val.2 ≤ b j
    · simp [hi]
    · have heq : {p | p ∈ certificateSet b g (e i) → b (e i).val.2 ≤ b j} =
          (certificateSet b g (e i))ᶜ := by ext p; simp [hi]
      rw [heq]
      exact (certificateSet_isClopen b g (e i)).compl.isOpen

omit [TopologicalSpace D] [Topology.IsScott D univ] in
theorem nextDomainCandidate_cover (hB : IsDomainBasis (range b))
    (e : ℕ → DomainCertificate b g) (n : ℕ) (h : DomainApproximation b g) (p : E) :
    ∃ j, p ∈ nextDomainCandidate b g e n h j := by
  classical
  let s := (Finset.range n).filter (fun i => p ∈ certificateSet b g (e i))
  have hr : ∀ i ∈ s, b (e i).val.2 ∈ basisApproximants (range b) (g p) := by
    intro i hi
    exact ⟨mem_range_self _,(e i).property p (Finset.mem_filter.mp hi).2⟩
  obtain ⟨u,hu,hpu,hru⟩ := hB.finite_bound
    (show b (h.val p) ∈ basisApproximants (range b) (g p) from ⟨mem_range_self _,h.property.2 p⟩)
    (fun i => b (e i).val.2) s hr
  obtain ⟨v,⟨j,rfl⟩,huv,hvx⟩ := hB.interpolate hu.2
  refine ⟨j,hvx,huv.mono hpu le_rfl,?_⟩
  intro i hin hi
  exact (hru i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,hi⟩)).trans (domainWayBelow_le huv)

/-- One continuous refinement step, with a finite certificate fairness bound. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    They also cover $E$. At a given $q$, directedness supplies a basis approximant above both $b_{h_n(q)}$ and all
    $b_{k_i}$ with $i\le n$ and $q\in V_i$. Interpolation then gives a basis element way above this common bound and
    way below $\delta(q)$, providing a suitable index $j$.
    Apply \termuse{continuous choice from an open cover} once more to choose $h_{n+1}$ continuously with
    $q\in U_{h_{n+1}(q)}^n$. This ensures
    $$
    b_{h_n(q)}\ll b_{h_{n+1}(q)}\ll\delta(q),\qquad
    q\in V_i\Longrightarrow b_{k_i}\sqsubseteq b_{h_{i+1}(q)}.
    $$
    Thus every certificate that applies to the input is absorbed at a finite stage.
-/
theorem exists_nextDomainApproximation (hB : IsDomainBasis (range b)) (hg : Continuous g)
    (e : ℕ → DomainCertificate b g) (n : ℕ) (h : DomainApproximation b g) :
    ∃ k : DomainApproximation b g,
      (∀ p, DomainWayBelow (b (h.val p)) (b (k.val p))) ∧
      ∀ p i, i < n → p ∈ certificateSet b g (e i) → b (e i).val.2 ≤ b (k.val p) := by
  obtain ⟨k,hk,hspec⟩ := exists_continuous_open_choice (nextDomainCandidate b g e n h)
    (nextDomainCandidate_isOpen b g hB hg e n h) (nextDomainCandidate_cover b g hB e n h)
  exact ⟨⟨k,hk,fun p => (hspec p).1⟩,fun p => (hspec p).2.1,fun p => (hspec p).2.2⟩

end Basis
section ChainLifting
variable {D : Type*} [OmegaCompletePartialOrder D]
variable [TopologicalSpace D] [Topology.IsScott D univ]

/-- Translate an arbitrary continuous partial map into way-below-increasing
basis chains. Every certified approximant is absorbed at a finite stage. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Set $g(q)(n):=h_n(q)$. Each coordinate is continuous, so $g:E\to\BaireSpace$ is continuous.
    For every $b_k\ll\delta(q)$ there is a certificate with $k_i=k$ and $q\in V_i$; the displayed inequality puts
    $b_k$ below a member of the output chain. Hence this chain is cofinal among the basis approximants of $\delta(q)$,
    and
    $$
    \DomainRepresentation{X}(g(q))=\DirectedSup_n b_{h_n(q)}=\delta(q).
    $$
    In particular, $g(q)$ is a valid name whose supremum lies in $X$. This proves the required lifting property and hence
    admissibility. All cylinder enumerations, basis relations, and choices here are fixed topological data; they are not
    assumed to be computable.
-/
theorem basisNameSup_lifts_partial (b : ℕ → D) (hB : IsDomainBasis (range b))
    {E : Set baire_space} (δ : E → D) (hδ : Continuous δ) :
    ∃ g : E → basisChainNames b, Continuous g ∧ ∀ p, basisNameSup b (g p) = δ p := by
  classical
  by_cases hE : Nonempty E
  · let := hE
    obtain ⟨h0⟩ := exists_domainApproximation b δ hB hδ
    let p0 : E := Classical.arbitrary E
    obtain ⟨v,_,_⟩ := exists_domainCertificate b δ hB hδ p0 (h0.val p0) (h0.property.2 p0)
    let : Nonempty (DomainCertificate b δ) := ⟨v⟩
    let : Countable (DomainCertificate b δ) := by unfold DomainCertificate; infer_instance
    obtain ⟨e,he⟩ := exists_surjective_nat (DomainCertificate b δ)
    let step (n : ℕ) (h : DomainApproximation b δ) : DomainApproximation b δ :=
      (exists_nextDomainApproximation b δ hB hδ e (n+1) h).choose
    have hstep (n : ℕ) (h : DomainApproximation b δ) :
        (∀ p, DomainWayBelow (b (h.val p)) (b ((step n h).val p))) ∧
        ∀ p i, i < n+1 → p ∈ certificateSet b δ (e i) → b (e i).val.2 ≤ b ((step n h).val p) :=
      (exists_nextDomainApproximation b δ hB hδ e (n+1) h).choose_spec
    let H : ℕ → DomainApproximation b δ := Nat.rec h0 step
    have Hstep (n : ℕ) (p : E) : DomainWayBelow (b ((H n).val p)) (b ((H (n+1)).val p)) :=
      (hstep n (H n)).1 p
    have Hfair (p : E) (i : ℕ) (hi : p ∈ certificateSet b δ (e i)) :
        b (e i).val.2 ≤ b ((H (i+1)).val p) :=
      (hstep i (H i)).2 p i (Nat.lt_succ_self i) hi
    let names : E → baire_space := fun p n => (H n).val p
    have hn (p : E) : names p ∈ basisChainNames b := fun n => Hstep n p
    let g : E → basisChainNames b := fun p => ⟨names p,hn p⟩
    refine ⟨g,(continuous_pi (fun n => (H n).property.1)).subtype_mk _,?_⟩
    intro p
    apply (basisNameSup_isLUB b (g p)).unique
    constructor
    · rintro a ⟨n,rfl⟩
      exact domainWayBelow_le ((H n).property.2 p)
    · intro y hy
      apply (hB (δ p)).2.2.2
      rintro a ⟨⟨k,rfl⟩,hk⟩
      obtain ⟨v,hvk,hpv⟩ := exists_domainCertificate b δ hB hδ p k hk
      obtain ⟨i,rfl⟩ := he v
      rw [← hvk]
      exact (Hfair p i hpv).trans (hy ⟨i+1,rfl⟩)
  · let : IsEmpty E := not_nonempty_iff.mp hE
    exact ⟨fun p => isEmptyElim p,continuous_iff_continuousAt.mpr (fun p => isEmptyElim p),
      fun p => isEmptyElim p⟩

/-- Names whose chain supremum lies in the designated subspace. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Here is the chain construction behind the theorem. Fix an embedding $X\IncludedIn D$ as a generalized $\bPi^0_2$
    subspace and a countable basis $\IndexedFamily{b_n}{n\in\omega}$ of $D$. Define
    $\PartialFunctionMap{\DomainRepresentation{X}}{\BaireSpace}{X}$ by declaring that $p$ is a name when
    $$
    b_{p(0)}\ll b_{p(1)}\ll b_{p(2)}\ll\cdots
    \qquad\text{and}\qquad
    \DirectedSup_n b_{p(n)}\in X,
    $$
    and then setting
    $$
    \DomainRepresentation{X}(p):=\DirectedSup_n b_{p(n)}.
    $$
-/
def restrictedBasisNames (b : ℕ → D) (A : Set D) : Set baire_space :=
  {p | ∃ h : p ∈ basisChainNames b, basisNameSup b ⟨p,h⟩ ∈ A}

noncomputable def restrictedBasisChain (b : ℕ → D) (A : Set D)
    (p : restrictedBasisNames b A) : basisChainNames b := ⟨p.val,p.property.choose⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Here is the chain construction behind the theorem. Fix an embedding $X\IncludedIn D$ as a generalized $\bPi^0_2$
    subspace and a countable basis $\IndexedFamily{b_n}{n\in\omega}$ of $D$. Define
    $\PartialFunctionMap{\DomainRepresentation{X}}{\BaireSpace}{X}$ by declaring that $p$ is a name when
    $$
    b_{p(0)}\ll b_{p(1)}\ll b_{p(2)}\ll\cdots
    \qquad\text{and}\qquad
    \DirectedSup_n b_{p(n)}\in X,
    $$
    and then setting
    $$
    \DomainRepresentation{X}(p):=\DirectedSup_n b_{p(n)}.
    $$
-/
noncomputable def restrictedBasisValue (b : ℕ → D) (A : Set D)
    (p : restrictedBasisNames b A) : A :=
  ⟨basisNameSup b (restrictedBasisChain b A p),p.property.choose_spec⟩

theorem restrictedBasisValue_continuous (b : ℕ → D) (A : Set D) :
    Continuous (restrictedBasisValue b A) :=
  ((basisNameSup_continuous b).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

omit [TopologicalSpace D] [Topology.IsScott D univ] in
theorem restrictedBasisValue_surjective (b : ℕ → D) (hB : IsDomainBasis (range b)) (A : Set D) :
    Surjective (restrictedBasisValue b A) := by
  intro x
  obtain ⟨p,hp⟩ := basisNameSup_surjective b hB x.val
  have hm : p.val ∈ restrictedBasisNames b A := ⟨p.property,hp ▸ x.property⟩
  refine ⟨⟨p.val,hm⟩,Subtype.ext ?_⟩
  exact hp

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    Here is the chain construction behind the theorem. Fix an embedding $X\IncludedIn D$ as a generalized $\bPi^0_2$
    subspace and a countable basis $\IndexedFamily{b_n}{n\in\omega}$ of $D$. Define
    $\PartialFunctionMap{\DomainRepresentation{X}}{\BaireSpace}{X}$ by declaring that $p$ is a name when
    $$
    b_{p(0)}\ll b_{p(1)}\ll b_{p(2)}\ll\cdots
    \qquad\text{and}\qquad
    \DirectedSup_n b_{p(n)}\in X,
    $$
    and then setting
    $$
    \DomainRepresentation{X}(p):=\DirectedSup_n b_{p(n)}.
    $$
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The two computational frameworks meet through representations by increasing chains of finite domain information.
-/
noncomputable def domainRepresentation (b : ℕ → D) (hB : IsDomainBasis (range b)) (A : Set D) :
    Representation A where
  domain := restrictedBasisNames b A
  toFun := restrictedBasisValue b A
  surjective := restrictedBasisValue_surjective b hB A

omit [TopologicalSpace D] [Topology.IsScott D univ] in
theorem restrictedBasisNames_eq_image (b : ℕ → D) (A : Set D) :
    restrictedBasisNames b A = Subtype.val '' ((basisNameSup b) ⁻¹' A) := by
  ext p
  constructor
  · rintro ⟨h,hm⟩
    exact ⟨⟨p,h⟩,hm,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨q.property,hq⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: proposition
  title: Admissibility of basis-chain names
-/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The remaining requirement that the supremum belong to $X$ is the inverse image of a generalized $\bPi^0_2$ set.
    Closure of that class under continuous preimages, followed by passage from the closed name space to the ambient
    Baire space, shows that the domain of names is $\bPi^0_2$.
-/
theorem domainRepresentation_domain_generalizedPi02 (b : ℕ → D)
    (hB : IsDomainBasis (range b)) {A : Set D} (hA : GeneralizedPi02 A) :
    GeneralizedPi02 (domainRepresentation b hB A).domain := by
  change GeneralizedPi02 (restrictedBasisNames b A)
  rw [restrictedBasisNames_eq_image]
  exact basisNameDomain_generalizedPi02 b hA

/-- The chain representation is admissible for every designated subspace,
without assuming that its points are maximal or that it is Hausdorff. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: proposition
  title: Admissibility of basis-chain names
-/
theorem domainRepresentation_isAdmissible (b : ℕ → D)
    (hB : IsDomainBasis (range b)) (A : Set D) :
    (domainRepresentation b hB A).IsAdmissible := by
  apply (admissible_iff_partial_lifting _).mpr
  refine ⟨restrictedBasisValue_continuous b A,?_⟩
  intro E g hg
  obtain ⟨f,hf,hcomm⟩ := basisNameSup_lifts_partial b hB
    (fun p => (g p).val) (continuous_subtype_val.comp hg)
  have hn (p : E) : (f p).val ∈ restrictedBasisNames b A :=
    ⟨(f p).property,(hcomm p) ▸ (g p).property⟩
  let k : E → restrictedBasisNames b A := fun p => ⟨(f p).val,hn p⟩
  refine ⟨k,(continuous_subtype_val.comp hf).subtype_mk _,?_⟩
  intro p
  apply Subtype.ext
  exact hcomm p

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    When $X$ is Polish, both $\DomainRepresentation{X}$ and the standard \termuse{Cauchy representation} $\rho_X$ are
    admissible. The Kreitz--Weihrauch theorem in §{sec:kreitz-weihrauch-admissibility} therefore gives
    $$
    \DomainRepresentation{X}\ContinuouslyEquivalentTo\rho_X.
    $$
-/
/-- In particular, the chain representation is equivalent to any admissible
Cauchy representation of the designated space. -/
theorem domainRepresentation_equivalent (b : ℕ → D)
    (hB : IsDomainBasis (range b)) (A : Set D) {ρ : Representation A}
    (hρ : ρ.IsAdmissible) : ContinuouslyEquivalent (domainRepresentation b hB A) ρ :=
  continuouslyEquivalent_of_admissible (domainRepresentation_isAdmissible b hB A) hρ

end ChainLifting

end PolishSpaceBook
