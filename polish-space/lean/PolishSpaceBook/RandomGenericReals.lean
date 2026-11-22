module

public import PolishSpaceBook.ForcingPolishSpaces
public import PolishSpaceBook.E0Nonsmooth

@[expose] public section

/-!
# Random filters, their actual reals, and Borel truth

Length partitions construct a unique real from the positive measure-algebra
filter. The cylinder truth equivalence is proved from directedness; it is not
an assumed atomic-truth interface. Borel truth then uses the explicit countable
decision tests. Set-theoretic models, names, and valuation remain separate.
-/

namespace PolishSpaceBook
open MeasureTheory Set Filter
open scoped ENNReal

variable {μ : Measure (ℕ → Bool)}

/-- The measure-algebra value of a basic cylinder. -/
def randomCylinder (μ : Measure (ℕ → Bool)) (s : List Bool) : MeasureAlgebra μ :=
  MeasureAlgebra.mk (cyl s) (isOpen_cyl s).measurableSet

/-- Every condition in this test decides a prefix of the specified length. -/
def randomLengthRequirement (μ : Measure (ℕ → Bool)) (n : ℕ) :
    Set (MeasureAlgebra.Positive μ) :=
  {p | ∃ s : List Bool, s.length = n ∧ p.val ≤ randomCylinder μ s}

theorem randomLengthRequirement_lower (n : ℕ) : IsLowerSet (randomLengthRequirement μ n) := by
  rintro p q hqp ⟨s, hs, hp⟩
  exact ⟨s, hs, le_trans hqp hp⟩

/-- A finite cylinder partition has supremum one in the measure algebra. -/
theorem iSup_randomCylinder [IsFiniteMeasure μ] (n : ℕ) :
    (⨆ s : Fin n → Bool, randomCylinder μ (List.ofFn s)) = ⊤ := by
  simp only [randomCylinder]
  rw [← MeasureAlgebra.mk_iUnion]
  have hcover : (⋃ s : Fin n → Bool, cyl (List.ofFn s)) = (univ : Set (ℕ → Bool)) := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨fun i => x i, mem_cyl_seqPrefix x n⟩
  simp only [hcover]
  rfl

/-- A positive condition meets some cell of each finite cylinder partition
in positive measure. Intersecting with that cell gives the required refinement. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cylinder partitions
-/
theorem randomLengthRequirement_dense [IsFiniteMeasure μ] (n : ℕ) :
    IsCoinitial (randomLengthRequirement μ n) := by
  intro p
  obtain ⟨s, hs⟩ := MeasureAlgebra.exists_positive_intersection
    (fun s : Fin n → Bool => randomCylinder μ (List.ofFn s)) p (by rw [iSup_randomCylinder]; exact le_top)
  refine ⟨⟨p.val ⊓ randomCylinder μ (List.ofFn s), hs⟩, ?_,
    (show p.val ⊓ randomCylinder μ (List.ofFn s) ≤ p.val from inf_le_left)⟩
  exact ⟨List.ofFn s, List.length_ofFn, inf_le_right⟩

/-- Prefix decisions made by some condition in the random filter. -/
def randomPrefixFilter (G : Order.PFilter (MeasureAlgebra.Positive μ)) : Set CohenCondition :=
  {s | ∃ p ∈ G, p.val ≤ randomCylinder μ s}

theorem randomCylinder_le_of_prefix {s t : List Bool} (h : s.IsPrefix t) :
    randomCylinder μ t ≤ randomCylinder μ s :=
  Eventually.of_forall (cyl_subset_of_prefix h)

/-- A positive common lower bound of cylinder classes gives an actual point
of their intersection, hence comparable finite prefixes. -/
theorem prefix_or_prefix_of_random_common_lower {s t : List Bool}
    (p : MeasureAlgebra.Positive μ) (hs : p.val ≤ randomCylinder μ s)
    (ht : p.val ≤ randomCylinder μ t) : s.IsPrefix t ∨ t.IsPrefix s := by
  have hn : (cyl s ∩ cyl t : Set (ℕ → Bool)).Nonempty := by
    by_contra he
    have hz := Set.not_nonempty_iff_eq_empty.mp he
    have hbot : randomCylinder μ s ⊓ randomCylinder μ t = ⊥ := by
      rw [randomCylinder, randomCylinder, MeasureAlgebra.mk_inf]
      apply (MeasureAlgebra.mk_eq_bot _ _).mpr
      simp [hz]
    apply p.property
    apply le_bot_iff.mp
    exact (le_inf hs ht).trans_eq hbot
  obtain ⟨x, hxs, hxt⟩ := hn
  have hprefix {u v : List Bool} (hu : x ∈ cyl u) (hv : x ∈ cyl v)
      (hl : u.length ≤ v.length) : u.IsPrefix v := by
    rw [List.prefix_iff_getElem]
    refine ⟨hl, ?_⟩
    intro i hi
    exact (hu i hi).symm.trans (hv i (lt_of_lt_of_le hi hl))
  rcases le_total s.length t.length with h | h
  · exact Or.inl (hprefix hxs hxt h)
  · exact Or.inr (hprefix hxt hxs h)

/-- The cylinder decisions form an ordinary prefix filter. -/
theorem randomPrefixFilter_isCohenFilter (G : Order.PFilter (MeasureAlgebra.Positive μ)) :
    IsCohenFilter (randomPrefixFilter G) := by
  rw [isCohenFilter_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := G.nonempty
    refine ⟨[], p, hp, ?_⟩
    have hnil : randomCylinder μ [] = ⊤ := by
      apply Quotient.sound
      exact Eventually.of_forall (fun x => by simp [cyl, prefixOfSeq])
    rw [hnil]
    exact le_top
  · rintro s ⟨p, hp, hps⟩ t hst
    exact ⟨p, hp, hps.trans (randomCylinder_le_of_prefix hst)⟩
  · rintro s ⟨p, hp, hps⟩ t ⟨q, hq, hqt⟩
    obtain ⟨r, _, hrp, hrq⟩ := G.directed p hp q hq
    rcases prefix_or_prefix_of_random_common_lower r (le_trans hrp hps) (le_trans hrq hqt) with h | h
    · exact ⟨t, ⟨q, hq, hqt⟩, h, by simp [CohenStronger]⟩
    · exact ⟨s, ⟨p, hp, hps⟩, by simp [CohenStronger], h⟩

/-- All length tests make the consistent cylinder decisions total. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Random filter union
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $H=\{s:\exists p\in G\ (p\le[\cyl{s}])\}$. It contains the empty string and every prefix of any of its members.
    If $s,t\in H$, choose witnessing conditions in $G$ and a common strengthening in $G$.
    This positive condition lies below both cylinder classes, so their intersection has positive measure and is nonempty.
    A point in the intersection extends both strings; hence one is a prefix of the other. The longer string is a common extension in $H$.
    Thus $H$ is a Cohen filter. Meeting every $C_n$ gives strings of every length in $H$.
    The Cohen filter union lemma yields a unique real whose prefixes are exactly $H$.
    Upward closure of $G$ gives $s\in H$ iff $[\cyl{s}]\in G$, proving the displayed equivalence.
    At each length the real has exactly one prefix, so the last assertions follow as well.
    \end{proof}
-/
theorem random_filter_existsUnique_real (G : Order.PFilter (MeasureAlgebra.Positive μ))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement μ n) :
    ∃! x : ℕ → Bool, ∀ s : List Bool,
      x ∈ cyl s ↔ ∃ p ∈ G, p.val ≤ randomCylinder μ s := by
  have hG := randomPrefixFilter_isCohenFilter G
  have hlength : ∀ n, ∃ s ∈ randomPrefixFilter G, s ∈ cohenLengthRequirement n := by
    intro n
    obtain ⟨p, hp, s, hs, hps⟩ := hlen (n + 1)
    exact ⟨s, ⟨p, hp, hps⟩, by change n < s.length; omega⟩
  obtain ⟨x, hx, hu⟩ := cohen_filter_existsUnique_real hG hlength
  have heq := cohen_filter_eq_prefixes hG hlength hx
  refine ⟨x, ?_, ?_⟩
  · intro s
    change s ∈ {s | prefixOfSeq s x} ↔ s ∈ randomPrefixFilter G
    rw [heq]
  · intro y hy
    apply hu y
    intro s hs
    exact (cohenAgrees_iff_prefixOfSeq s y).mpr ((hy s).mpr hs)

/-- The real is chosen from the unique consistent cylinder decisions. -/
noncomputable def randomFilterReal (G : Order.PFilter (MeasureAlgebra.Positive μ))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement μ n) : ℕ → Bool :=
  (random_filter_existsUnique_real G hlen).choose

theorem randomFilterReal_mem_cyl (G : Order.PFilter (MeasureAlgebra.Positive μ))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement μ n) (s : List Bool) :
    randomFilterReal G hlen ∈ cyl s ↔ ∃ p ∈ G, p.val ≤ randomCylinder μ s :=
  (random_filter_existsUnique_real G hlen).choose_spec.1 s

/-- The Rasiowa--Sikorski construction for a countable family of arbitrary
 dense sets. The upward closure of the descending chain retains the selected
 members themselves, so lower closure of the dense sets is not required. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The combined family of dense requirements is countable. Enumerate it, adding the whole order if necessary to handle an empty family.
    Start at the prescribed condition and successively choose a stronger condition in the next dense set.
    Take the upward closure of the resulting descending chain. Two members of this closure have a common strengthening farther along the chain,
    so it is a filter. The chosen condition in each dense set belongs to the filter itself; no closure assumption on the prescribed dense sets is needed.
    The length tests construct its real, and the Borel truth and null-set avoidance lemmas give the conclusions.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The dense subsets of $P$ belonging to $M$ form a countable family. Adjoin $P$ if necessary to make the family nonempty.
    Enumerate it as $\{D_n:n\in\omega\}$. Starting at the prescribed condition, choose
    $$p_{-1}\ge p_0\ge p_1\ge\cdots,\qquad p_n\in D_n,$$
    using density at each step, and put
    $$G:=\{q\in P:\exists n\in\omega\,(p_n\le q)\}.$$
    This set is upward closed. If $q,r\in G$ are witnessed by $n,m$, respectively, then $p_{\max\{n,m\}}$
    belongs to $G$ and is stronger than both. Thus $G$ is a filter. It contains $p_{-1}$ because $p_0\le p_{-1}$,
    and it meets every $D_n$ at $p_n$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Since $M$ is countable in the surrounding universe, enumerate there all its dense subsets of $P$ and apply the
    lemma. It produces an $M$-generic filter through any prescribed condition.
-/
theorem pfilter_meets_countable_dense {P : Type*} [Preorder P]
    (F : Set (Set P)) (hF : F.Countable) (hd : ∀ D ∈ F, IsCoinitial D) (p : P) :
    ∃ G : Order.PFilter P, p ∈ G ∧ ∀ D ∈ F, ∃ q ∈ G, q ∈ D := by
  classical
  obtain ⟨D, hD⟩ := (hF.insert univ).exists_eq_range ⟨univ, mem_insert _ _⟩
  have hdn (n) : IsCoinitial (D n) := by
    have hmem : D n ∈ insert univ F := hD ▸ mem_range_self n
    rcases hmem with h | h
    · rw [h]
      exact fun q => ⟨q, mem_univ q, le_rfl⟩
    · exact hd _ h
  choose step hstepmem hsteple using hdn
  let Q : ℕ → P := Nat.rec p (fun n q => step n q)
  have hQ : Antitone Q := antitone_nat_of_succ_le (fun n => hsteple n (Q n))
  let S : Set P := {q | ∃ n, Q n ≤ q}
  have hS : Order.IsPFilter S := Order.IsPFilter.of_def
    ⟨p, 0, le_rfl⟩
    (by
      rintro q ⟨n, hn⟩ r ⟨m, hm⟩
      exact ⟨Q (max n m), ⟨max n m, le_rfl⟩,
        (hQ (le_max_left _ _)).trans hn, (hQ (le_max_right _ _)).trans hm⟩)
    (by rintro q r hqr ⟨n, hn⟩; exact ⟨n, hn.trans hqr⟩)
  refine ⟨hS.toPFilter, ⟨0, le_rfl⟩, ?_⟩
  intro A hA
  obtain ⟨n, rfl⟩ := hD ▸ (mem_insert_of_mem univ hA)
  exact ⟨Q (n + 1), ⟨n + 1, le_rfl⟩, hstepmem n (Q n)⟩

/-- The explicit countable decision tests for a cylinder-based Borel code. -/
def randomCodeRequirements (μ : Measure (ℕ → Bool)) (s : ℕ → List Bool) (c : BorelCode) :
    Set (Set (MeasureAlgebra.Positive μ)) :=
  c.forcingRequirements (fun n => MeasureAlgebra.below (randomCylinder μ (s n)))

theorem randomCodeRequirements_countable (s : ℕ → List Bool) (c : BorelCode) :
    (randomCodeRequirements μ s c).Countable := c.forcingRequirements_countable _

theorem randomCodeRequirements_dense (s : ℕ → List Bool) (c : BorelCode) :
    ∀ D ∈ randomCodeRequirements μ s c, IsCoinitial D := by
  intro D hD
  exact (c.forcingRequirements_dense_lower _ (fun _ => MeasureAlgebra.below_lower _) D hD).1

/-- Actual Borel truth for the real constructed from the filter. Atomic truth
is supplied by the cylinder construction proved above, not by an extra premise. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Borel truth for a random filter
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induct on the code. For a cylinder leaf, the equivalence is the random filter union lemma and upward closure of the filter.
    At a complement node with child $d$, the filter meets $\ForcingDecision{\CodeForcingSet{d}}$.
    The positive and negative alternatives cannot both occur in the filter: a common strengthening would belong to the child's forcing set and also exclude every such strengthening.
    By the induction hypothesis, absence of a positive witness is exactly $r_G\notin B_d$.
    The decision test supplies a negative witness in that case, and the complement calculation identifies it with a condition below the complement class.

    At a union node with children $d_n$, put $S=\bigcup_n\CodeForcingSet{d_n}$.
    If $r_G$ belongs to one child's interpreted set, induction supplies a condition in that child's forcing set, hence one below the union class.
    Conversely, suppose $p\in G$ lies below the union class. Then $S$ is dense below $p$ by the positive-condition recursion lemma.
    Choose $q\in G\cap\ForcingDecision{S}$. If $q\in\ForcingNeg{S}$, a common strengthening of $p$ and $q$ can be further strengthened into $S$, a contradiction.
    Thus $q\in S$, so it belongs to some child's forcing set. Induction puts the real in that child's interpreted set and hence in the union.
    \end{proof}
-/
theorem randomFilterReal_borel_truth [IsFiniteMeasure μ]
    (G : Order.PFilter (MeasureAlgebra.Positive μ))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement μ n)
    (s : ℕ → List Bool) (c : BorelCode)
    (hG : ∀ D ∈ randomCodeRequirements μ s c, ∃ p ∈ G, p ∈ D) :
    randomFilterReal G hlen ∈ c.decode (fun n => cyl (s n)) ↔
      ∃ p ∈ G, p.val ≤ MeasureAlgebra.mk (c.decode (fun n => cyl (s n)))
        (c.measurable_decode _ (fun n => (isOpen_cyl (s n)).measurableSet)) := by
  have h := c.forcing_truth (fun n => cyl (s n))
    (fun n => MeasureAlgebra.below (randomCylinder μ (s n)))
    (fun _ => MeasureAlgebra.below_lower _) G (randomFilterReal G hlen)
    (fun n => randomFilterReal_mem_cyl G hlen (s n)) hG
  rw [c.random_forcing_eq_below] at h
  simp only [randomCylinder, c.measureValue_eq_mk_decode] at h
  exact h

/-- Null Borel codes cannot contain the real of a filter meeting their truth tests. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: corollary
  title: Local null-set avoidance
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Otherwise the truth lemma supplies a positive condition below $[B_c]=0$, which is impossible.
    For a singleton, a code is given by the intersection of the cylinders of all finite prefixes of the point.
    Their measures tend to zero, so the singleton is null. Meeting its tests therefore excludes that point.
    \end{proof}
-/
theorem randomFilterReal_avoids_null [IsFiniteMeasure μ]
    (G : Order.PFilter (MeasureAlgebra.Positive μ))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement μ n)
    (s : ℕ → List Bool) (c : BorelCode)
    (hG : ∀ D ∈ randomCodeRequirements μ s c, ∃ p ∈ G, p ∈ D)
    (hnull : μ (c.decode (fun n => cyl (s n))) = 0) :
    randomFilterReal G hlen ∉ c.decode (fun n => cyl (s n)) := by
  intro hx
  obtain ⟨p, _, hp⟩ := (randomFilterReal_borel_truth G hlen s c hG).mp hx
  have hzero := (MeasureAlgebra.mk_eq_bot _
    (c.measurable_decode _ (fun n => (isOpen_cyl (s n)).measurableSet))).mpr hnull
  exact p.property (le_bot_iff.mp (hp.trans_eq hzero))

/-- A random filter may meet prescribed dense sets, all length tests, and the
Borel truth tests of any prescribed countable family of codes simultaneously. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Countable random requirements
-/
theorem exists_random_filter_for_codes [IsFiniteMeasure μ]
    (F : Set (Set (MeasureAlgebra.Positive μ))) (hF : F.Countable)
    (hd : ∀ D ∈ F, IsCoinitial D) (s : ℕ → List Bool)
    (C : Set BorelCode) (hC : C.Countable) (p : MeasureAlgebra.Positive μ) :
    ∃ G : Order.PFilter (MeasureAlgebra.Positive μ), p ∈ G ∧
      (∀ D ∈ F, ∃ q ∈ G, q ∈ D) ∧
      (∀ n, ∃ q ∈ G, q ∈ randomLengthRequirement μ n) ∧
      ∀ c ∈ C, ∀ D ∈ randomCodeRequirements μ s c, ∃ q ∈ G, q ∈ D := by
  let R := ⋃ c ∈ C, randomCodeRequirements μ s c
  have hRc : R.Countable := hC.biUnion fun c _ => randomCodeRequirements_countable s c
  have hRd : ∀ D ∈ R, IsCoinitial D := by
    intro D hD
    obtain ⟨c, hc, hDc⟩ := mem_iUnion₂.mp hD
    exact randomCodeRequirements_dense s c D hDc
  obtain ⟨G, hp, hm⟩ := pfilter_meets_countable_dense
    (F ∪ range (randomLengthRequirement μ) ∪ R)
    ((hF.union (countable_range _)).union hRc)
    (by
      intro D hD
      rcases hD with (hD | hD) | hD
      · exact hd D hD
      · obtain ⟨n, rfl⟩ := hD
        exact randomLengthRequirement_dense n
      · exact hRd D hD) p
  exact ⟨G, hp, fun D hD => hm D (Or.inl (Or.inl hD)),
    fun n => hm _ (Or.inl (Or.inr (mem_range_self n))),
    fun c hc D hD => hm D (Or.inr (mem_iUnion₂.mpr ⟨c, hc, hD⟩))⟩

/-- The finite-coordinate product calculation gives each cylinder its usual mass. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cylinder partitions
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    A cylinder of length $n$ prescribes $n$ independent bits, each with probability $1/2$, so its measure is $2^{-n}$.
    Distinct cylinders of that length are disjoint, and together they partition Cantor space.
    Every positive-measure Borel set has positive-measure intersection with one cell of this finite partition.
    Intersecting with that cell gives a condition in $C_n$ below the original condition, proving density and maximality.
    The definition of $C_n$ also shows that it is closed under strengthening.
    \end{proof}
-/
theorem fairCoinProduct_cyl (s : List Bool) :
    fairCoinProduct (cyl s) = (1 / 2 : ℝ≥0∞) ^ s.length := by
  obtain ⟨x, hx⟩ := cyl_nonempty s
  have hpi : cyl s = Set.pi (↑(Finset.range s.length) : Set ℕ) (fun i => {x i}) := by
    ext y
    constructor
    · intro hy i hi
      have hi' : i < s.length := Finset.mem_range.mp hi
      exact (hy i hi').trans (hx i hi').symm
    · intro hy i hi
      exact (hy i (Finset.mem_range.mpr hi)).trans (hx i hi)
  rw [hpi, fairCoinProduct, Measure.infinitePi_pi _ (by measurability)]
  simp [fairCoin_singleton]

/-- Every cylinder is a positive condition for the fair-coin measure. -/
noncomputable def randomCoinCylinder (s : List Bool) : MeasureAlgebra.Positive fairCoinProduct :=
  ⟨randomCylinder fairCoinProduct s, by
    intro h
    have hz := (MeasureAlgebra.mk_eq_bot (cyl s) (isOpen_cyl s).measurableSet).mp h
    rw [fairCoinProduct_cyl] at hz
    exact (pow_ne_zero _ (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)) hz⟩

/-- Distinct equal-length cylinder conditions have no common positive refinement. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cylinder partitions
-/
theorem randomCoinCylinder_incompatible {s t : List Bool}
    (hlen : s.length = t.length) (hne : s ≠ t) :
    ¬ ∃ p : MeasureAlgebra.Positive fairCoinProduct,
      p ≤ randomCoinCylinder s ∧ p ≤ randomCoinCylinder t := by
  rintro ⟨p, hs, ht⟩
  rcases prefix_or_prefix_of_random_common_lower p hs ht with h | h
  · exact hne (h.eq_of_length_le hlen.ge)
  · exact hne (h.eq_of_length_le hlen.le).symm

/-- Maximality of the cylinder antichain: every positive condition is
compatible with a cylinder of each specified length. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Cylinder partitions
-/
theorem randomCoinCylinder_maximal (n : ℕ) (p : MeasureAlgebra.Positive fairCoinProduct) :
    ∃ s : List Bool, s.length = n ∧ ∃ q : MeasureAlgebra.Positive fairCoinProduct,
      q ≤ p ∧ q ≤ randomCoinCylinder s := by
  obtain ⟨q, ⟨s, hs, hqs⟩, hqp⟩ := randomLengthRequirement_dense n p
  exact ⟨s, hs, q, hqp, hqs⟩

/-- In the fair-coin order, atomic truth is membership of the cylinder condition
itself in the filter, by upward closure. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Random filter union
-/
theorem randomCoinFilterReal_mem_cyl (G : Order.PFilter (MeasureAlgebra.Positive fairCoinProduct))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement fairCoinProduct n) (s : List Bool) :
    randomFilterReal G hlen ∈ cyl s ↔ randomCoinCylinder s ∈ G := by
  rw [randomFilterReal_mem_cyl]
  constructor
  · rintro ⟨p, hp, hps⟩
    exact G.mem_of_le (show p ≤ randomCoinCylinder s from hps) hp
  · intro hs
    exact ⟨randomCoinCylinder s, hs, le_rfl⟩

/-- At every length the filter chooses exactly one cylinder. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Random filter union
-/
theorem randomCoinFilter_unique_cylinder
    (G : Order.PFilter (MeasureAlgebra.Positive fairCoinProduct))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement fairCoinProduct n) (n : ℕ) :
    ∃! s : {s : List Bool // s.length = n}, randomCoinCylinder s.val ∈ G := by
  let x := randomFilterReal G hlen
  refine ⟨⟨seqPrefix x n, seqPrefix_length x n⟩, ?_, ?_⟩
  · exact (randomCoinFilterReal_mem_cyl G hlen _).mp (mem_cyl_seqPrefix x n)
  · intro s hs
    apply Subtype.ext
    have hx := (randomCoinFilterReal_mem_cyl G hlen s.val).mpr hs
    have heq := seqPrefix_eq_of_mem_cyl hx
    simpa only [s.property] using heq.symm

/-- A fixed enumeration of all finite binary strings for cylinder-based codes. -/
def randomCylinderWord (n : ℕ) : List Bool := (Encodable.decode (α := List Bool) n).getD []

@[simp] theorem randomCylinderWord_encode (s : List Bool) :
    randomCylinderWord (Encodable.encode s) = s := by
  simp [randomCylinderWord]

/-- A singleton is the intersection of all cylinders of its finite prefixes. -/
def randomSingletonCode (x : ℕ → Bool) : BorelCode :=
  .compl (.union fun n => .compl (.leaf (Encodable.encode (seqPrefix x n))))

theorem randomSingletonCode_decode (x : ℕ → Bool) :
    (randomSingletonCode x).decode (fun n => cyl (randomCylinderWord n)) = {x} := by
  ext y
  simp only [randomSingletonCode, BorelCode.decode, randomCylinderWord_encode,
    mem_compl_iff, mem_iUnion, not_exists, not_not, mem_singleton_iff]
  constructor
  · intro h
    funext i
    have hi := h (i + 1) i (by simp)
    exact hi.trans (seqPrefix_get x _)
  · rintro rfl n
    exact mem_cyl_seqPrefix _ n

/-- Singleton tests exclude any prescribed real; the fair-coin product has no atoms. -/
theorem randomCoinFilterReal_ne
    (G : Order.PFilter (MeasureAlgebra.Positive fairCoinProduct))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement fairCoinProduct n)
    (x : ℕ → Bool)
    (hG : ∀ D ∈ randomCodeRequirements fairCoinProduct randomCylinderWord (randomSingletonCode x),
      ∃ p ∈ G, p ∈ D) : randomFilterReal G hlen ≠ x := by
  have h := randomFilterReal_avoids_null G hlen randomCylinderWord (randomSingletonCode x) hG
    (by rw [randomSingletonCode_decode]; exact measure_singleton x)
  simpa only [randomSingletonCode_decode, mem_singleton_iff] using h

end PolishSpaceBook
