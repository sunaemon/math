module

public import PolishSpaceBook.CantorDerivativeTree

@[expose] public section

/-! # Tree codes for transfinite Cantor--Bendixson recursion

A stage intersects the original tree with the derivative codes of every
predecessor. This single recursion has the usual initial, successor and
limit equations and retains every perfect subset of the initial body.
-/
namespace PolishSpaceBook.CantorDerivative
open Set

variable {ι : Type*} (R : ι → ι → Prop) (hR : WellFounded R)
  (T : Set (List Bool))

noncomputable def stageTree : ι → Set (List Bool) :=
  hR.fix fun a previous => T ∩ {s | ∀ (b : ι) (h : R b a), s ∈ derivativeTree (previous b h)}

theorem stageTree_eq (a : ι) :
    stageTree R hR T a = T ∩ {s | ∀ b, R b a → s ∈ derivativeTree (stageTree R hR T b)} := by
  unfold stageTree
  rw [WellFounded.fix_eq]

theorem stageTree_isSubtree (hT : IsSubtree T) (a : ι) :
    IsSubtree (stageTree R hR T a) := by
  rw [stageTree_eq]
  intro s t ht hst
  exact ⟨hT ht.1 hst, fun b hb => derivativeTree_isSubtree _ (ht.2 b hb) hst⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Intersections preserve downward closure. A sequence belongs to the body of an intersection of trees
    exactly when all its prefixes belong to every tree, so taking bodies commutes with arbitrary
    intersections. The one-step result identifies each derivative-tree body with the corresponding
    derived set. This proves the displayed equation. If another family satisfies that equation,
    well-founded induction identifies its predecessor sets and hence its set at the current stage.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
-/
theorem stageTree_body (a : ι) :
    treeBody (stageTree R hR T a) = treeBody T ∩
      {x | ∀ b, R b a → x ∈ derivedSet (treeBody (stageTree R hR T b))} := by
  ext x
  rw [stageTree_eq]
  change (∀ n, seqPrefix x n ∈ T ∧ ∀ b, R b a →
    seqPrefix x n ∈ derivativeTree (stageTree R hR T b)) ↔ _
  constructor
  · intro hx
    refine ⟨fun n => (hx n).1, fun b hb => ?_⟩
    rw [← derivativeTree_body]
    exact fun n => (hx n).2 b hb
  · rintro ⟨hxT, hx⟩ n
    refine ⟨hxT n, fun b hb => ?_⟩
    have h := hx b hb
    rw [← derivativeTree_body] at h
    exact h n

theorem stageBody_subset_initial (a : ι) : treeBody (stageTree R hR T a) ⊆ treeBody T := by
  rw [stageTree_body]
  exact inter_subset_left

theorem stageBody_subset_derivative {a b : ι} (hba : R b a) :
    treeBody (stageTree R hR T a) ⊆ derivedSet (treeBody (stageTree R hR T b)) := by
  rw [stageTree_body R hR T a]
  exact fun _ hx => hx.2 b hba

theorem stageBody_antitone {a b : ι} (hba : R b a) :
    treeBody (stageTree R hR T a) ⊆ treeBody (stageTree R hR T b) :=
  (stageBody_subset_derivative R hR T hba).trans
    ((isClosed_iff_derivedSet_subset _).mp (isClosed_treeBody _))

theorem stageTree_minimal (a : ι) (ha : ∀ b, ¬ R b a) : stageTree R hR T a = T := by
  rw [stageTree_eq]
  ext s
  simp [ha]

/-- The predecessor condition is the order-theoretic description of a successor stage. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    All stage bodies are closed. Thus $\eta\prec\xi$ implies
    $$F_\xi\IncludedIn\cbderivative{F_\eta}\IncludedIn F_\eta.$$
    At a successor of $\eta$, the factor $\cbderivative{F_\eta}$ is contained in $F$ and in every earlier
    derivative factor, by monotonicity of the derived-set operation. It therefore equals the whole
    intersection. At a limit, every predecessor $\eta$ has a later predecessor $\zeta$. A point belonging to
    all predecessor bodies belongs to $F_\zeta\IncludedIn\cbderivative{F_\eta}$ for each such $\eta$, proving
    the reverse inclusion in the limit equation. Nonzero limits have a predecessor, whose body is
    already contained in the original set. Empty predecessor families instead give the initial stage.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
-/
theorem stageBody_successor (a b : ι) (hba : R b a)
    (ha : ∀ c, R c a → c = b ∨ R c b) :
    treeBody (stageTree R hR T a) = derivedSet (treeBody (stageTree R hR T b)) := by
  apply Subset.antisymm (stageBody_subset_derivative R hR T hba)
  intro x hx
  rw [stageTree_body]
  have hxb : x ∈ treeBody (stageTree R hR T b) :=
    (isClosed_iff_derivedSet_subset _).mp (isClosed_treeBody _) hx
  refine ⟨stageBody_subset_initial R hR T b hxb, fun c hc => ?_⟩
  rcases ha c hc with rfl | hcb
  · exact hx
  · exact derivedSet_mono _ _ (stageBody_antitone R hR T hcb) hx

/-- At a limit every predecessor has a later predecessor; no cofinal sequence is selected. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    All stage bodies are closed. Thus $\eta\prec\xi$ implies
    $$F_\xi\IncludedIn\cbderivative{F_\eta}\IncludedIn F_\eta.$$
    At a successor of $\eta$, the factor $\cbderivative{F_\eta}$ is contained in $F$ and in every earlier
    derivative factor, by monotonicity of the derived-set operation. It therefore equals the whole
    intersection. At a limit, every predecessor $\eta$ has a later predecessor $\zeta$. A point belonging to
    all predecessor bodies belongs to $F_\zeta\IncludedIn\cbderivative{F_\eta}$ for each such $\eta$, proving
    the reverse inclusion in the limit equation. Nonzero limits have a predecessor, whose body is
    already contained in the original set. Empty predecessor families instead give the initial stage.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
-/
theorem stageBody_limit (a : ι)
    (ha : ∀ b, R b a → ∃ c, R c a ∧ R b c) :
    treeBody (stageTree R hR T a) = treeBody T ∩
      {x | ∀ b, R b a → x ∈ treeBody (stageTree R hR T b)} := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨stageBody_subset_initial R hR T a hx,
      fun b hb => stageBody_antitone R hR T hb hx⟩
  · rintro x ⟨hxT, hx⟩
    rw [stageTree_body]
    refine ⟨hxT, fun b hb => ?_⟩
    obtain ⟨c, hca, hbc⟩ := ha b hb
    exact stageBody_subset_derivative R hR T hbc (hx c hca)

theorem stageBody_nonzero_limit (a : ι) (hne : ∃ b, R b a)
    (ha : ∀ b, R b a → ∃ c, R c a ∧ R b c) :
    treeBody (stageTree R hR T a) = {x | ∀ b, R b a → x ∈ treeBody (stageTree R hR T b)} := by
  rw [stageBody_limit R hR T a ha]
  apply inter_eq_right.mpr
  intro x hx
  obtain ⟨b,hb⟩ := hne
  exact stageBody_subset_initial R hR T b (hx b hb)

theorem perfect_subset_stage {P : Set (ℕ → Bool)} (hP : Perfect P) (hPT : P ⊆ treeBody T)
    (a : ι) : P ⊆ treeBody (stageTree R hR T a) := by
  induction a using hR.induction with
  | h a ih =>
    rw [stageTree_body]
    intro x hx
    refine ⟨hPT hx, fun b hb => ?_⟩
    exact derivedSet_mono _ _ (ih b hb) ((perfect_iff_eq_derivedSet.mp hP) ▸ hx)

/-- The displayed recursion determines every stage uniquely. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
-/
theorem stageBody_unique (H : ι → Set (ℕ → Bool))
    (hH : ∀ a, H a = treeBody T ∩ {x | ∀ b, R b a → x ∈ derivedSet (H b)})
    (a : ι) : H a = treeBody (stageTree R hR T a) := by
  induction a using hR.induction with
  | h a ih =>
    rw [hH a,stageTree_body]
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro b
    apply imp_congr_right
    intro hb
    rw [ih b hb]

/-- A stable stage is the greatest perfect subset of the original closed set. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    If $P\IncludedIn F$ is perfect, well-founded induction gives $P\IncludedIn F_\eta$ at every stage:
    use $P=\cbderivative{P}$ and monotonicity to place it in each predecessor derivative.
    If a stage equals its own derivative, it is closed and has no isolated points, hence is perfect.
    It contains every perfect subset by the preceding induction and is therefore the perfect kernel.
    At a later stage the decreasing property gives one inclusion, and preservation of this perfect
    subset gives the other.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
-/
theorem stable_stage_greatest (a : ι)
    (ha : treeBody (stageTree R hR T a) = derivedSet (treeBody (stageTree R hR T a))) :
    Perfect (treeBody (stageTree R hR T a)) ∧
      treeBody (stageTree R hR T a) ⊆ treeBody T ∧
      ∀ P : Set (ℕ → Bool), Perfect P → P ⊆ treeBody T → P ⊆ treeBody (stageTree R hR T a) :=
  ⟨perfect_iff_eq_derivedSet.mpr ha, stageBody_subset_initial R hR T a,
    fun _ hP hPT => perfect_subset_stage R hR T hP hPT a⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
-/
theorem stable_stage_persists {a b : ι} (hab : R a b)
    (ha : treeBody (stageTree R hR T a) = derivedSet (treeBody (stageTree R hR T a))) :
    treeBody (stageTree R hR T b) = treeBody (stageTree R hR T a) :=
  Subset.antisymm (stageBody_antitone R hR T hab)
    (perfect_subset_stage R hR T (perfect_iff_eq_derivedSet.mpr ha)
      (stageBody_subset_initial R hR T a) b)

end PolishSpaceBook.CantorDerivative
