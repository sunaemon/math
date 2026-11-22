module

public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Homeomorph.Lemmas
public import PolishSpaceBook.KolmogorovTail

@[expose] public section

/-!
# Rectangles and the topological zero-one law

The rectangle lemma allows an arbitrary second factor. Its proof uses a
countable closed nowhere-dense cover and a countable base in the Baire factor.
-/

noncomputable section

namespace PolishSpaceBook.TopologicalTail

open Set Filter Topology TopologicalSpace MeasurableSpace MeasureTheory

section Rectangles

variable {P Y : Type*} [TopologicalSpace P] [TopologicalSpace Y]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For the forward direction, cover $W\times B$ by closed nowhere-dense sets $F_n$.
    Choose a countable base of nonempty open sets $U_m$ in $P$, and put
    $$D_{n,m}:=\{y\in Y:U_m\times\{y\}\IncludedIn F_n\}.$$
    Each $D_{n,m}$ is closed, since it is the intersection, over $p\in U_m$, of the inverse images of $F_n$
    under the continuous maps $y\mapsto(p,y)$. If $D_{n,m}$ contained a nonempty open set $V$, then
    $U_m\times V$ would be a nonempty open subset of $F_n$, contrary to nowhere density.
    Thus every $D_{n,m}$ is nowhere dense.
-/
/-- The parameters whose section of `F` contains the entire open set `U`. -/
def verticalCore (F : Set (P × Y)) (U : Set P) : Set Y :=
  {y | ∀ p ∈ U, (p, y) ∈ F}

lemma verticalCore_closed {F : Set (P × Y)} (hF : IsClosed F) (U : Set P) :
    IsClosed (verticalCore F U) := by
  have heq : verticalCore F U = ⋂ p ∈ U, (fun y => (p, y)) ⁻¹' F := by
    ext y
    simp [verticalCore]
  rw [heq]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    hF.preimage (continuous_const.prodMk continuous_id)

lemma verticalCore_nowhereDense {F : Set (P × Y)} (hF : IsClosed F)
    (hFn : IsNowhereDense F) {U : Set P} (hU : IsOpen U) (hne : U.Nonempty) :
    IsNowhereDense (verticalCore F U) := by
  rw [(verticalCore_closed hF U).isNowhereDense_iff]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨p, hp⟩ := hne
  have hsub : U ×ˢ interior (verticalCore F U) ⊆ F := by
    rintro ⟨p, y⟩ ⟨hp, hy⟩
    exact (interior_subset hy) p hp
  have hmem : (p, y) ∈ interior F :=
    interior_maximal hsub (hU.prod isOpen_interior) ⟨hp, hy⟩
  simp only [hF.isNowhereDense_iff.mp hFn, mem_empty_iff_false] at hmem

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: lemma
  title: Kuratowski--Ulam rectangle consequence
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For $y\in B$, the closed sections $\{p\in P:(p,y)\in F_n\}$ cover $W$.
    Since $W$ is not meager, at least one section has nonempty interior and hence contains some $U_m$.
    Consequently $y\in D_{n,m}$, and
    $$B\IncludedIn\bigcup_{n,m}D_{n,m}.$$
    This proves that $B$ is meager. Conversely, the product with $P$ of any nowhere-dense subset of $Y$ is nowhere dense
    in $P\times Y$. Applying this to a countable nowhere-dense cover of $B$ shows that $P\times B$, and hence
    $W\times B$, is meager.
-/
/-- A rectangle with a nonmeager first factor is meager exactly when its
second factor is meager; no definability condition is imposed on either set. -/
theorem rectangle_meagre_iff_of_not_meagre [SecondCountableTopology P]
    {W : Set P} (hW : ¬ IsMeagre W) (B : Set Y) : IsMeagre (W ×ˢ B) ↔ IsMeagre B := by
  classical
  constructor
  · intro h
    obtain ⟨S, hS, hc, hcover⟩ := isMeagre_iff_countable_union_isNowhereDense.mp h
    have : Countable S := hc
    let F : S → Set (P × Y) := fun i => closure i.val
    have hFc (i : S) : IsClosed (F i) := isClosed_closure
    have hFn (i : S) : IsNowhereDense (F i) := (hS i.val i.property).closure
    obtain ⟨U, hU⟩ := exists_seq_basis P
    have hcores : IsMeagre (⋃ i : S, ⋃ n : ℕ, ⋃ (_ : (U n).Nonempty), verticalCore (F i) (U n)) := by
      apply isMeagre_iUnion
      intro i
      apply isMeagre_iUnion
      intro n
      exact isMeagre_iUnion fun hn =>
        (verticalCore_nowhereDense (hFc i) (hFn i) (hU.isOpen (mem_range_self n)) hn).isMeagre
    apply hcores.mono
    intro y hy
    have hsections : W ⊆ ⋃ i : S, (fun p => (p, y)) ⁻¹' F i := by
      intro p hp
      obtain ⟨s, hs, hps⟩ := mem_sUnion.mp (hcover (show (p, y) ∈ W ×ˢ B from ⟨hp, hy⟩))
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, subset_closure hps⟩
    have hsome : ∃ i : S, (interior ((fun p => (p, y)) ⁻¹' F i)).Nonempty := by
      by_contra hnone
      push Not at hnone
      have hm : IsMeagre (⋃ i : S, (fun p => (p, y)) ⁻¹' F i) := by
        apply isMeagre_iUnion
        intro i
        apply IsNowhereDense.isMeagre
        have hc : IsClosed ((fun p => (p, y)) ⁻¹' F i) :=
          (hFc i).preimage (continuous_id.prodMk continuous_const)
        exact hc.isNowhereDense_iff.mpr (hnone i)
      exact hW (hm.mono hsections)
    obtain ⟨i, p, hp⟩ := hsome
    obtain ⟨V, ⟨n, rfl⟩, hpV, hV⟩ := hU.exists_subset_of_mem_open hp isOpen_interior
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨p, hpV⟩,
      fun q hq => interior_subset (s := (fun p => (p, y)) ⁻¹' F i) (hV hq)⟩⟩⟩
  · intro h
    exact (h.preimage_of_isOpenMap (α := P × Y) continuous_snd isOpenMap_snd).mono
      (fun _ hx => hx.2)

/-- The rectangle consequence used in the book, including arbitrary second factors. -/
theorem rectangle_meagre_iff [Nonempty P] [BaireSpace P] [SecondCountableTopology P]
    (B : Set Y) : IsMeagre ((univ : Set P) ×ˢ B) ↔ IsMeagre B :=
  rectangle_meagre_iff_of_not_meagre
    (not_isMeagre_of_isOpen isOpen_univ univ_nonempty) B

end Rectangles

section TailSets

variable {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]

/-- Membership is invariant under changing any finite prefix. -/
def IsTailSet (A : Set (∀ n, X n)) : Prop :=
  ∀ N x y, (∀ n, N ≤ n → x n = y n) → (x ∈ A ↔ y ∈ A)

/-- Split a sequence into its prefix and its remaining coordinates. -/
def prefixSplit (N : ℕ) :
    (∀ n, X n) ≃ₜ (∀ n : {n // n < N}, X n) × (∀ n : {n // ¬ n < N}, X n) :=
  Homeomorph.piEquivPiSubtypeProd (fun n => n < N) X

lemma tail_same_section {A : Set (∀ n, X n)} (hA : IsTailSet A) (N : ℕ)
    (p q : ∀ n : {n // n < N}, X n) (y : ∀ n : {n // ¬ n < N}, X n) :
    (prefixSplit N).symm (p, y) ∈ A ↔ (prefixSplit N).symm (q, y) ∈ A := by
  apply hA N
  intro n hn
  simp [prefixSplit, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, not_lt.mpr hn]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    $$A = P_N \times A_N, \qquad V \cap A = \prod_{n < N} V_n \times A_N.$$
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Set $P_N := \prod_{n < N} X_n$ and $Y_N := \prod_{n \ge N} X_n$. Tail-invariance gives a set-theoretic decomposition:
    there is a set $A_N \IncludedIn Y_N$ such that
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Indeed, put $y \in A_N$ iff $(p,y) \in A$ for some, equivalently every, $p \in P_N$. No Borel or Baire-property claim
    about $A_N$ is needed.
-/
/-- A tail set is a full prefix factor times an arbitrary tail section. -/
lemma tail_decomposition {A : Set (∀ n, X n)} (hA : IsTailSet A) (N : ℕ)
    (p : ∀ n : {n // n < N}, X n) :
    (prefixSplit N).symm ⁻¹' A =
      univ ×ˢ {y | (prefixSplit N).symm (p, y) ∈ A} := by
  ext z
  simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_ofPred_eq]
  exact tail_same_section hA N z.1 p z.2

section Measurable

variable [mX : ∀ n, MeasurableSpace (X n)]

/-- Restriction to the coordinates starting at `N`. -/
def tailRestriction (N : ℕ) (x : ∀ n, X n) : ∀ n : {n // ¬ n < N}, X n := fun n => x n

omit [∀ n, TopologicalSpace (X n)] in
lemma tailFrom_eq_comap (N : ℕ) :
    KolmogorovTail.tailFrom (KolmogorovTail.coordinateSigma (X := X)) N =
      MeasurableSpace.comap (tailRestriction (X := X) N) inferInstance := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def, tailRestriction, iSup_subtype, not_lt,
    KolmogorovTail.tailFrom, KolmogorovTail.coordinateSigma]

omit [∀ n, TopologicalSpace (X n)] in
/-- A measurable tail event cannot distinguish sequences with the same tail. -/
lemma isTailSet_of_tail_measurable {A : Set (∀ n, X n)}
    (hA : MeasurableSet[KolmogorovTail.tail (KolmogorovTail.coordinateSigma (X := X))] A) :
    IsTailSet A := by
  intro N x y hxy
  have hN : MeasurableSet[KolmogorovTail.tailFrom (KolmogorovTail.coordinateSigma (X := X)) N] A :=
    (show KolmogorovTail.tail (KolmogorovTail.coordinateSigma (X := X)) ≤
      KolmogorovTail.tailFrom (KolmogorovTail.coordinateSigma (X := X)) N from iInf_le _ N) A hA
  rw [tailFrom_eq_comap] at hN
  obtain ⟨B, _, hB⟩ := hN
  rw [← hB]
  change tailRestriction N x ∈ B ↔ tailRestriction N y ∈ B
  have heq : tailRestriction N x = tailRestriction N y :=
    funext fun n => hxy n (not_lt.mp n.property)
  rw [heq]

/-- Measurability of the section obtained by fixing one prefix. -/
lemma measurable_prefix_section (N : ℕ) (p : ∀ n : {n // n < N}, X n) :
    Measurable (fun y => (prefixSplit N).symm (p, y)) := by
  apply measurable_pi_iff.mpr
  intro n
  by_cases hn : n < N
  · simp [prefixSplit, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hn]
  · simpa [prefixSplit, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hn]
      using (measurable_pi_apply (⟨n, hn⟩ : {n // ¬ n < N}))

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For an arbitrary subset $A\IncludedIn\prod_nX_n$, say that $A$ is a \termdefine{tail set} if changing finitely many
    coordinates does not change membership in $A$. For Borel $A$, this is equivalent to $A\in\mathcal T$.
    Indeed, tail invariance writes $A$ as the inverse image, under restriction to the remaining coordinates, of its
    Borel section at any fixed finite prefix. Thus $A\in\sigma(\pi_n:n\ge N)$ for every $N$.
    Conversely, a member of $\sigma(\pi_n:n\ge N)$ cannot distinguish points that agree at all coordinates $n\ge N$.
    Membership in $\mathcal T$ therefore implies tail invariance.
-/
/-- For measurable sets, finite-prefix invariance is exactly tail measurability. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For a product space $X = \prod_n X_n$ with product probability measure $\mu = \prod_n \mu_n$, the
    \termdefineas{tail sigma-algebra}{tail $\sigma$-algebra} is
    $$\mathcal T \;:=\; \bigcap_{N \in \omega}\, \sigma(\pi_n : n \ge N),$$
    the Borel events whose membership is unaffected by altering any finite prefix.
-/
theorem tail_measurable_iff {A : Set (∀ n, X n)} :
    MeasurableSet[KolmogorovTail.tail (KolmogorovTail.coordinateSigma (X := X))] A ↔
      MeasurableSet A ∧ IsTailSet A := by
  constructor
  · intro hA
    exact ⟨KolmogorovTail.tail_le_iSup _ A hA, isTailSet_of_tail_measurable hA⟩
  · rintro ⟨hA, ht⟩
    by_cases hne : A.Nonempty
    · obtain ⟨x₀, _⟩ := hne
      apply MeasurableSpace.measurableSet_iInf.mpr
      intro N
      rw [tailFrom_eq_comap]
      let p : ∀ n : {n // n < N}, X n := fun n => x₀ n
      let B := {y | (prefixSplit N).symm (p, y) ∈ A}
      refine ⟨B, hA.preimage (measurable_prefix_section N p), ?_⟩
      ext x
      change (prefixSplit N).symm (p, tailRestriction N x) ∈ A ↔ x ∈ A
      apply ht N
      intro n hn
      simp [prefixSplit, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
        tailRestriction, not_lt.mpr hn]
    · rw [not_nonempty_iff_eq_empty.mp hne]
      exact @MeasurableSet.empty _ (KolmogorovTail.tail (KolmogorovTail.coordinateSigma (X := X)))

end Measurable

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    $$V \;=\; \prod_{n < N} V_n \;\times\; \prod_{n \ge N} X_n$$
-/
/-- Every nonempty open set contains a box restricting only a finite prefix. -/
lemma exists_prefix_box {U : Set (∀ n, X n)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (N : ℕ) (W : Set (∀ n : {n // n < N}, X n)),
      IsOpen W ∧ W.Nonempty ∧ W ×ˢ univ ⊆ (prefixSplit N).symm ⁻¹' U := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  let N := I.sup id + 1
  have hbound (i : I) : (i : ℕ) < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
  let W : Set (∀ n : {n // n < N}, X n) :=
    ⋂ i : I, (fun p => p ⟨i, hbound i⟩) ⁻¹' u i
  refine ⟨N, W, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i => (hu i i.property).1.preimage
      (continuous_apply (⟨i, hbound i⟩ : {n // n < N}))
  · refine ⟨fun i => x i, ?_⟩
    exact mem_iInter.mpr fun i => (hu i i.property).2
  · rintro ⟨p, y⟩ ⟨hp, _⟩
    apply hsub
    intro i hi
    have hm := mem_iInter.mp hp ⟨i, hi⟩
    simpa [prefixSplit, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      hbound ⟨i, hi⟩] using hm

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Topological 0-1 law
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $A \IncludedIn X$ be a tail set with the Baire property, and suppose $A$ is non-meager. We
    show that $A$ is
    comeager.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    By the BP, $A = U \triangle M$ for some open $U$ and meager $M$. Non-meagerness of $A$ forces $U$ to be nonempty, so $U$
    contains some basic open box
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    with each $V_n \IncludedIn X_n$ a nonempty open set. Since $V \IncludedIn U$,
    $$\SetDifference{V}{A} \;\IncludedIn\; M,$$
    which is meager. Hence $A$ is comeager in $V$.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Compute
    $$\SetDifference{V}{A} \;=\; \prod_{n < N} V_n \;\times\; \Big(\SetDifference{\prod_{n \ge N} X_n}{A_N}\Big).$$
    The first factor $\prod_{n<N}V_n$ is a nonempty open subset of $P_N$, so the Baire category theorem says that it is
    not meager in $P_N$. Apply the \termuseas{Kuratowski--Ulam rectangle lemma}{rectangle lemma} in $P_N\times Y_N$.
    It follows that $\SetDifference{\prod_{n \ge N} X_n}{A_N}$ is meager, or equivalently that $A_N$ is comeager in the
    tail factor.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Now expand the global complement:
    $$\SetDifference{X}{A} \;=\; \prod_{n < N} X_n \;\times\; \Big(\SetDifference{\prod_{n \ge N} X_n}{A_N}\Big).$$
    The same rectangle consequence shows the complement is meager, since the right factor is meager. Therefore $A$ is
    comeager.
-/
/-- The topological zero-one law, with no Borel assumption on the tail set. -/
theorem zero_one [∀ n, PolishSpace (X n)] [∀ n, Nonempty (X n)]
    {A : Set (∀ n, X n)} (hA : IsTailSet A) (hBP : BaireMeasurableSet A) :
    IsMeagre A ∨ IsMeagre Aᶜ := by
  classical
  by_cases hmeagre : IsMeagre A
  · exact Or.inl hmeagre
  right
  obtain ⟨U, hU, hEq⟩ := hBP.residualEq_isOpen
  have hDiff : IsMeagre (U \ A) := by
    change (U \ A)ᶜ ∈ residual (∀ n, X n)
    filter_upwards [Filter.eventuallyEqSet_iff.mp hEq] with x hx
    simp only [mem_compl_iff, Set.mem_sdiff]
    tauto
  have hne : U.Nonempty := by
    by_contra hn
    have hEmpty : U = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hmeagre
    change Aᶜ ∈ residual (∀ n, X n)
    filter_upwards [Filter.eventuallyEqSet_iff.mp hEq] with x hx
    simpa [hEmpty] using hx
  obtain ⟨N, W, hWo, hWne, hbox⟩ := exists_prefix_box hU hne
  let e := prefixSplit (X := X) N
  let p : ∀ n : {n // n < N}, X n := fun n => Classical.arbitrary (X n)
  let B := {y | e.symm (p, y) ∈ A}
  have hdecomp : e.symm ⁻¹' A = univ ×ˢ B := tail_decomposition hA N p
  have hrect : IsMeagre (W ×ˢ Bᶜ) := by
    apply (hDiff.preimage_of_isOpenMap e.symm.continuous e.symm.isOpenMap).mono
    rintro z ⟨hw, hb⟩
    refine ⟨hbox ⟨hw, mem_univ _⟩, ?_⟩
    intro hz
    have hz' : z ∈ e.symm ⁻¹' A := hz
    rw [hdecomp] at hz'
    exact hb hz'.2
  have hB : IsMeagre Bᶜ :=
    (rectangle_meagre_iff_of_not_meagre (not_isMeagre_of_isOpen hWo hWne) Bᶜ).mp hrect
  have hall : IsMeagre ((univ : Set (∀ n : {n // n < N}, X n)) ×ˢ Bᶜ) :=
    (rectangle_meagre_iff Bᶜ).mpr hB
  apply (hall.preimage_of_isOpenMap e.continuous e.isOpenMap).mono
  intro x hx
  refine ⟨mem_univ _, ?_⟩
  intro hb
  have hz : e x ∈ e.symm ⁻¹' A := by rw [hdecomp]; exact ⟨mem_univ _, hb⟩
  exact hx (by simpa using hz)

end TailSets

end PolishSpaceBook.TopologicalTail
