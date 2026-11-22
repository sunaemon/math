module

public import PolishSpaceBook.Determinacy
public import Mathlib.Topology.Piecewise

@[expose] public section

/-!
# Wadge hierarchy

Formalization targets for `polish-space/src/polish-space-book/wadge-hierarchy.md`.

Formalized here are Wadge reducibility and equivalence, reflexivity,
transitivity, complement duality, the trivial and nontrivial clopen degrees,
the countable-disjointification proof of clopen approximation, preservation of
closedness under Wadge reduction, and the coarse reduction relation obtained
by identifying a set with its complement.

WadgeGamePayoff supplies the G-delta productive-play subspace, continuous
pass deletion, Borelness of both payoffs, and their integer-game presentation.
WadgeStrategyReduction extracts both continuous reductions and proves Wadge's
lemma and Borel semi-linearity. WadgeContinuousStrategy constructs the converse
second-player strategy, completing the strategy correspondence.
WadgeOpenDegrees supplies the explicit open and closed complete sets and the
first-one map witnessing the reverse reduction to any non-closed open set.
WadgeSecondLevel constructs the clopen row coding for the Sigma-0-2 and Pi-0-2
complete sets and derives their strictness from the finite Borel diagonal.
HausdorffDifference supplies the countable difference levels and their Delta-0-2
inclusion. HausdorffBoundary proves countable termination of the closed boundary
derivative and constructs the open sets for both sides of every removed layer.
HausdorffRepresentation interleaves these opens, identifies their first-entry
pieces, and completes Hausdorff's representation theorem. MartinMonk constructs
the simultaneous causal array and its Borel flip set, and proves well-foundedness
using the imported Borel-determinacy theorem and its strategy transport. The global degree structure and
stronger-determinacy material are survey scope and are explicitly exempted.
-/

namespace PolishSpaceBook

noncomputable section

universe u v w

open Function Set Topology

section Reducibility

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For $A \IncludedIn X$ and $B \IncludedIn Y$ with $X, Y$ zero-dimensional Polish, $A$
    **\termdefineas{Wadge reducibility}{Wadge-reduces}** to $B$, written $A \le_W B$, if there exists a continuous map $f :
    X \to Y$ with
    $$A \;=\; f^{-1}(B).$$
-/
/-- `A` Wadge-reduces to `B` when `A` is the preimage of `B` under a
continuous map. The definition makes sense on arbitrary topological spaces. -/
def WadgeReducible (A : Set X) (B : Set Y) : Prop :=
  ∃ f : X → Y, Continuous f ∧ A = f ⁻¹' B

/-- Wadge equivalence is reducibility in both directions. -/
def WadgeEquivalent (A : Set X) (B : Set Y) : Prop :=
  WadgeReducible A B ∧ WadgeReducible B A

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    *Self-dual vs non-self-dual.* A Wadge degree $[A]_W$ is \termdefine{self-dual} if $A \equiv_W \SetDifference{X}{A}$,
    otherwise
    \termdefine{non-self-dual}.
-/
/-- A set is self-dual when it is Wadge-equivalent to its complement. -/
def IsSelfDual (A : Set X) : Prop :=
  WadgeEquivalent A Aᶜ

/-- A set is non-self-dual when it is not self-dual. -/
def IsNonSelfDual (A : Set X) : Prop :=
  ¬ IsSelfDual A

theorem WadgeReducible.refl (A : Set X) :
    WadgeReducible A A :=
  ⟨id, continuous_id, by simp⟩

theorem WadgeReducible.trans {A : Set X} {B : Set Y} {C : Set Z}
    (hAB : WadgeReducible A B) (hBC : WadgeReducible B C) :
    WadgeReducible A C := by
  obtain ⟨f, hf, hAf⟩ := hAB
  obtain ⟨g, hg, hBg⟩ := hBC
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  rw [hAf, hBg]
  rfl

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Thus $A$ is "no harder than $B$ up to a continuous renaming of points." The relation is reflexive and transitive, hence
    a quasi-order on subsets of zero-dimensional Polish spaces, with associated equivalence $A \equiv_W B$ and
    \termdefine{Wadge degree} $[A]_W$.
-/
/-- Wadge reducibility is a quasi-order on subsets of one fixed space. -/
theorem wadgeReducible_quasiOrder :
    (∀ A : Set X, WadgeReducible A A) ∧
      (∀ A B C : Set X,
        WadgeReducible A B → WadgeReducible B C → WadgeReducible A C) :=
  ⟨WadgeReducible.refl, fun _ _ _ ↦ WadgeReducible.trans⟩

/-- A reduction also reduces the two complements by the same map. -/
theorem WadgeReducible.compl {A : Set X} {B : Set Y}
    (hAB : WadgeReducible A B) :
    WadgeReducible Aᶜ Bᶜ := by
  obtain ⟨f, hf, hAf⟩ := hAB
  refine ⟨f, hf, ?_⟩
  simpa only [preimage_compl] using congrArg (fun S : Set X ↦ Sᶜ) hAf

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Wadge degrees come paired with their duals;
-/
/-- Complementation preserves equivalence of representatives. -/
theorem WadgeEquivalent.compl {A : Set X} {B : Set Y}
    (h : WadgeEquivalent A B) : WadgeEquivalent Aᶜ Bᶜ :=
  ⟨h.1.compl, h.2.compl⟩

theorem wadgeReducible_compl_iff {A : Set X} {B : Set Y} :
    WadgeReducible Aᶜ Bᶜ ↔ WadgeReducible A B := by
  constructor
  · intro h
    simpa using h.compl
  · exact WadgeReducible.compl

theorem isOpen_of_wadgeReducible {A : Set X} {B : Set Y}
    (hAB : WadgeReducible A B) (hB : IsOpen B) :
    IsOpen A := by
  obtain ⟨f, hf, rfl⟩ := hAB
  exact hB.preimage hf

theorem isClosed_of_wadgeReducible {A : Set X} {B : Set Y}
    (hAB : WadgeReducible A B) (hB : IsClosed B) :
    IsClosed A := by
  obtain ⟨f, hf, rfl⟩ := hAB
  exact hB.preimage hf

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For a pointclass $\Gamma$, write $\check\Gamma := \{\SetDifference{X}{A} : A \in \Gamma\}$ for the
    **\termdefine{dual class}**.
-/
/-- The pointclass obtained by complementing every member. -/
def DualPointclass (Γ : Set (Set X)) : Set (Set X) := Set.compl '' Γ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    A
    self-dual degree is one on which a continuous self-map can swap "in" and "out" of $A$.
-/
/-- Complementing a reduction supplies the reverse reduction, so one
membership-reversing continuous map suffices for self-duality. -/
theorem isSelfDual_iff_reduction_to_compl (A : Set X) :
    IsSelfDual A ↔ WadgeReducible A Aᶜ := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by simpa only [compl_compl] using h.compl⟩

end Reducibility

section ClopenDegrees

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

theorem wadgeReducible_empty_iff [Nonempty Y] (A : Set X) :
    WadgeReducible A (∅ : Set Y) ↔ A = ∅ := by
  constructor
  · rintro ⟨f, _hf, hA⟩
    simpa using hA
  · rintro rfl
    let y : Y := Classical.choice inferInstance
    exact ⟨fun _ ↦ y, continuous_const, by simp⟩

theorem wadgeReducible_univ_iff [Nonempty Y] (A : Set X) :
    WadgeReducible A (univ : Set Y) ↔ A = univ := by
  constructor
  · rintro ⟨f, _hf, hA⟩
    simpa using hA
  · rintro rfl
    let y : Y := Classical.choice inferInstance
    exact ⟨fun _ ↦ y, continuous_const, by simp⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For nonempty $X$, the trivial degrees $[\emptyset]_W$ and $[X]_W$ are non-self-dual and
    mutually dual.
-/
/-- Neither trivial degree is self-dual on a nonempty space. -/
theorem trivial_degrees_nonselfdual [Nonempty X] :
    IsNonSelfDual (∅ : Set X) ∧ IsNonSelfDual (univ : Set X) := by
  constructor
  · intro h
    have he := (wadgeReducible_univ_iff (∅ : Set X)).mp
      (by simpa only [compl_empty] using h.1)
    exact Set.empty_ne_univ he
  · intro h
    have he := (wadgeReducible_empty_iff (univ : Set X)).mp
      (by simpa only [compl_univ] using h.1)
    exact Set.empty_ne_univ he.symm

/-- A clopen set reduces to any nonempty proper set by a two-valued
continuous map. -/
theorem wadgeReducible_of_isClopen {C : Set X} {D : Set Y}
    (hC : IsClopen C) (hD : D.Nonempty) (hDc : Dᶜ.Nonempty) :
    WadgeReducible C D := by
  obtain ⟨d₁, hd₁⟩ := hD
  obtain ⟨d₀, hd₀c⟩ := hDc
  have hd₀ : d₀ ∉ D := hd₀c
  classical
  let f : X → Y := C.piecewise (fun _ ↦ d₁) (fun _ ↦ d₀)
  have hf : Continuous f := by
    apply Continuous.piecewise
    · intro x hx
      exfalso
      rw [hC.frontier_eq] at hx
      exact hx
    · exact continuous_const
    · exact continuous_const
  refine ⟨f, hf, ?_⟩
  ext x
  by_cases hx : x ∈ C
  · simp [f, hx, hd₁]
  · simp [f, hx, hd₀]

theorem wadgeEquivalent_clopen {C : Set X} {D : Set Y}
    (hC : IsClopen C) (hCne : C.Nonempty) (hCc : Cᶜ.Nonempty)
    (hD : IsClopen D) (hDne : D.Nonempty) (hDc : Dᶜ.Nonempty) :
    WadgeEquivalent C D :=
  ⟨wadgeReducible_of_isClopen hC hDne hDc,
    wadgeReducible_of_isClopen hD hCne hCc⟩

theorem wadgeEquivalent_compl_of_isClopen {C : Set X}
    (hC : IsClopen C) (hCne : C.Nonempty) (hCc : Cᶜ.Nonempty) :
    WadgeEquivalent C Cᶜ := by
  apply wadgeEquivalent_clopen hC hCne hCc hC.compl hCc
  simpa using hCne

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: proposition
  title: trivial and clopen degrees
-/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The first claim is immediate: the only continuous preimage of $\emptyset$ is $\emptyset$, and the
    only continuous preimage of a full space is a full space.

    For the second claim, let $C\IncludedIn X$ and $D\IncludedIn Y$ be nonempty proper clopen sets. Choose points $d_1\in D$
    and
    $d_0\in \SetDifference{Y}{D}$. The map
    $$
    f(x)=
    \begin{cases}
    d_1, & x\in C,\\
    d_0, & x\notin C
    \end{cases}
    $$
    is continuous because $C$ is clopen, and $C=f^{-1}(D)$. Thus $C\le_W D$. The reverse reduction is identical, so
    $C\equiv_W D$.

    For self-duality, apply the same argument with $D=\SetDifference{Y}{C}$ when $Y=X$. A nonempty proper clopen set and its
    complement are Wadge-equivalent.
    \end{proof}
-/
/-- The three conclusions of the book's proposition on the trivial and
nontrivial clopen degrees. The topological assumptions there are stronger than
needed for this elementary argument. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Typical examples are
    nonempty proper clopen sets
-/
theorem trivial_and_clopen_degrees [Nonempty X]
    {C : Set X} {D : Set Y}
    (hC : IsClopen C) (hCne : C.Nonempty) (hCc : Cᶜ.Nonempty)
    (hD : IsClopen D) (hDne : D.Nonempty) (hDc : Dᶜ.Nonempty) :
    WadgeReducible (∅ : Set X) (∅ : Set X) ∧
      WadgeReducible (univ : Set X) (univ : Set X) ∧
        WadgeEquivalent C D ∧ IsSelfDual C :=
  ⟨WadgeReducible.refl ∅, WadgeReducible.refl univ,
    wadgeEquivalent_clopen hC hCne hCc hD hDne hDc,
    wadgeEquivalent_compl_of_isClopen hC hCne hCc⟩

end ClopenDegrees

section ClopenApproximation

variable {X : Type u} [TopologicalSpace X] [SecondCountableTopology X]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: lemma
  title: clopen approximation lemma
-/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] The two open sets $O$ and $\SetDifference{X}{F}$ cover $X$. Since clopen sets form a base, every
    point has a clopen neighborhood contained in one of these two sets. Second countability gives Lindelöfness, so choose a
    countable clopen cover $\Sequence{E_k}{k\in\omega}$ of this form. Assign $E_k$ to $O$ whenever $E_k\IncludedIn O$,
    and otherwise to $\SetDifference{X}{F}$.
    Disjointify the cover by putting
    $$
    W_k:=\SetDifference{E_k}{\bigcup_{j<k}E_j}.
    $$
    Each $W_k$ is clopen because it is a finite Boolean combination of clopen sets. Every point belongs to the unique
    $W_k$ indexed by the least $k$ for which it belongs to $E_k$, so these sets partition $X$. Define
    $$
    V:=\bigcup_{\{k:E_k\IncludedIn O\}}W_k,\qquad
    \SetDifference{X}{V}=\bigcup_{\{k:\neg(E_k\IncludedIn O)\}}W_k.
    $$
    Both unions are open, so $V$ is clopen. A point of $F$ cannot first occur in an $E_k$ assigned to
    $\SetDifference{X}{F}$, while every selected $W_k$ lies in $O$. Therefore $F\IncludedIn V\IncludedIn O$.
    \end{proof}
-/
/-- Choose a countable clopen cover subordinate to the two open sets, then
assign each point to the first member of that cover containing it. -/
theorem exists_clopen_between (hzero : IsZeroDimensional X)
    {F O : Set X} (hF : IsClosed F) (hO : IsOpen O) (hFO : F ⊆ O) :
    ∃ V, IsClopen V ∧ F ⊆ V ∧ V ⊆ O := by
  classical
  let CoverPiece := {E : Set X // IsClopen E ∧ (E ⊆ O ∨ E ⊆ Fᶜ)}
  let : Nonempty CoverPiece := ⟨⟨∅, isClopen_empty, Or.inl (empty_subset _)⟩⟩
  have hcover : (univ : Set X) ⊆ ⋃ E : CoverPiece, E.val := by
    intro x _
    by_cases hx : x ∈ O
    · obtain ⟨E, hE, hxE, hEO⟩ := hzero.exists_subset_of_mem_open hx hO
      exact mem_iUnion.mpr ⟨⟨E, hE, Or.inl hEO⟩, hxE⟩
    · have hxF : x ∈ Fᶜ := fun h => hx (hFO h)
      obtain ⟨E, hE, hxE, hEF⟩ := hzero.exists_subset_of_mem_open hxF hF.isOpen_compl
      exact mem_iUnion.mpr ⟨⟨E, hE, Or.inr hEF⟩, hxE⟩
  obtain ⟨C, hC⟩ := (HereditarilyLindelofSpace.isLindelof (univ : Set X)).indexed_countable_subcover
    (fun E : CoverPiece => E.val) (fun E => E.property.1.isOpen) hcover
  let E : ℕ → Set X := fun n => (C n).val
  let W := disjointSeq E
  have hW : ∀ n, IsClopen (W n) := disjointSeq_isClopen (fun n => (C n).property.1)
  have hpart : ∀ x : X, ∃ n, x ∈ W n := by
    intro x
    apply mem_iUnion.mp
    rw [show (⋃ n, W n) = ⋃ n, E n from iUnion_disjointSeq_eq_iUnion E]
    exact hC (mem_univ x)
  let V := ⋃ n, ⋃ (_ : E n ⊆ O), W n
  have hcompl : Vᶜ = ⋃ n, ⋃ (_ : ¬ E n ⊆ O), W n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := hpart x
      have hn : ¬ E n ⊆ O := fun h => hx (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨h, hxn⟩⟩)
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, hxn⟩⟩
    · intro hx hxV
      obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
      obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hxV
      have hne : n ≠ m := by rintro rfl; exact hn hm
      exact Set.disjoint_left.mp (disjointSeq_pairwiseDisjoint E hne) hxn hxm
  have hVopen : IsOpen V := isOpen_iUnion fun n => isOpen_iUnion fun _ => (hW n).isOpen
  have hVclosed : IsClosed V := by
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun n => isOpen_iUnion fun _ => (hW n).isOpen
  refine ⟨V, ⟨hVclosed, hVopen⟩, ?_, ?_⟩
  · intro x hxF
    obtain ⟨n, hxn⟩ := hpart x
    have hn : E n ⊆ O := by
      rcases (C n).property.2 with h | h
      · exact h
      · exact (h (disjointSeq_subset E n hxn) hxF).elim
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, hxn⟩⟩
  · intro x hxV
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hxV
    exact hn (disjointSeq_subset E n hxn)

end ClopenApproximation

section CoarseDegrees

variable {X : Type u} [TopologicalSpace X]

/-- The Wadge class of a representative. -/
def WadgeClass (A : Set X) : Set (Set X) := {B | WadgeEquivalent B A}

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    It is cleaner to state the well-foundedness result on
    **\termdefineas{coarse Wadge degree}{coarse Wadge degrees}**, where a set is identified with its complement:
    $$A^\ast := [A]_W \cup [\SetDifference{\BaireSpace}{A}]_W.$$
-/
/-- A coarse class is the union of a degree and its complemented degree. -/
def CoarseWadgeClass (A : Set X) : Set (Set X) := WadgeClass A ∪ WadgeClass Aᶜ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Put $A^\ast \le_W^\ast B^\ast$ iff $A \le_W B$ or $A \le_W \SetDifference{\BaireSpace}{B}$.
-/
/-- Coarse Wadge reducibility, where the target may be replaced by its
complement. -/
def CoarseWadgeReducible (A B : Set X) : Prop :=
  WadgeReducible A B ∨ WadgeReducible A Bᶜ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The same continuous map reduces complements whenever it reduces the original sets. Composing reductions and
    using this complement law shows that the relation on representatives is reflexive and transitive.
    Write $A\preceq B$ for this relation. We claim that $A\preceq B$ and $B\preceq A$ hold exactly when
    $A\equiv_W B$ or $A\equiv_W\SetDifference{\BaireSpace}{B}$.
    If the two reductions use the same complement parity, their composition gives the required mutual reductions
    directly. If their parities differ, composition gives $A\le_W\SetDifference{\BaireSpace}{A}$ and
    $B\le_W\SetDifference{\BaireSpace}{B}$. Complementing these reductions makes both sets self-dual,
    so the complement choices can be removed and again yield mutual reductions. The converse is immediate.
    Thus mutual coarse reducibility means precisely equality of coarse degrees. Transitivity now also shows that
    replacing either representative within its coarse degree preserves the relation, and proves antisymmetry on
    those degrees. No determinacy assumption is needed for these facts. Wadge's lemma supplies the remaining
    comparability assertion for Borel sets.
    \end{proof}
-/
/-- Coarse reducibility composes, with complementation parity carried through. -/
theorem CoarseWadgeReducible.trans {A B C : Set X}
    (hAB : CoarseWadgeReducible A B) (hBC : CoarseWadgeReducible B C) :
    CoarseWadgeReducible A C := by
  rcases hAB with hAB | hAB <;> rcases hBC with hBC | hBC
  · exact Or.inl (hAB.trans hBC)
  · exact Or.inr (hAB.trans hBC)
  · exact Or.inr (hAB.trans hBC.compl)
  · exact Or.inl (by simpa using hAB.trans hBC.compl)

/-- Mutual coarse reducibility is equivalence up to complementation. -/
theorem coarseWadge_mutual_iff (A B : Set X) :
    (CoarseWadgeReducible A B ∧ CoarseWadgeReducible B A) ↔
      WadgeEquivalent A B ∨ WadgeEquivalent A Bᶜ := by
  constructor
  · rintro ⟨hAB, hBA⟩
    rcases hAB with hAB | hAB <;> rcases hBA with hBA | hBA
    · exact Or.inl ⟨hAB, hBA⟩
    · exact Or.inl ⟨hAB, hBA.trans (by simpa using (hAB.trans hBA).compl)⟩
    · exact Or.inr ⟨hAB, hBA.compl.trans ((by simpa using hAB.compl) : WadgeReducible Aᶜ B) |>.trans hBA⟩
    · exact Or.inr ⟨hAB, by simpa using hBA.compl⟩
  · rintro (⟨hAB, hBA⟩ | ⟨hAB, hBA⟩)
    · exact ⟨Or.inl hAB, Or.inl hBA⟩
    · exact ⟨Or.inr hAB, Or.inr (by simpa using hBA.compl)⟩

/-- Changing either representative within its coarse degree preserves the order. -/
theorem coarseWadge_representatives {A A' B B' : Set X}
    (hA : CoarseWadgeReducible A A' ∧ CoarseWadgeReducible A' A)
    (hB : CoarseWadgeReducible B B' ∧ CoarseWadgeReducible B' B) :
    CoarseWadgeReducible A B ↔ CoarseWadgeReducible A' B' :=
  ⟨fun h => hA.2.trans (h.trans hB.1), fun h => hA.1.trans (h.trans hB.2)⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{coarse Wadge order}{Coarse Wadge order}]
    This relation is independent of representatives and is a partial order on coarse Wadge degrees.
    For Borel sets it is linear by Wadge's lemma.
    \end{lemma*}
-/
/-- The semi-linear principle immediately makes coarse reducibility total. -/
theorem coarseWadge_linear_of_semilinear
    (hSLO : ∀ A B : Set X, WadgeReducible A B ∨ WadgeReducible B Aᶜ)
    (A B : Set X) :
    CoarseWadgeReducible A B ∨ CoarseWadgeReducible B A := by
  rcases hSLO A B with hAB | hBA
  · exact Or.inl (Or.inl hAB)
  · exact Or.inr (Or.inr hBA)

end CoarseDegrees

end

end PolishSpaceBook
