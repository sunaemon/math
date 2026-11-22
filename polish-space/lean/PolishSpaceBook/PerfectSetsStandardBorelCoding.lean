module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Real.Cardinality
public import PolishSpaceBook.FiniteBorelUniversal
public import PolishSpaceBook.EffrosBorelTrees
public import PolishSpaceBook.BorelCodeCardinality
public import PolishSpaceBook.CantorBendixsonStages
public import PolishSpaceBook.PerfectCantorScheme
public import PolishSpaceBook.CantorBaireBorelIsomorphism

@[expose] public section

/-!
# Perfect sets and standard Borel coding

Formalization targets for
`polish-space/src/polish-space-book/perfect-sets-standard-borel-coding.md`.

Borel Schröder--Bernstein follows the book's iterates and piecewise maps.
Cantor--Bendixson now uses the actual transfinite derivative construction:
`CantorBendixsonStages` proves the recursion laws, stabilization, countability
of the first stable ordinal and of the scattered part, and preservation of
all perfect subsets. Uniqueness uses the book's perfect-set argument on a
closed perfect subset of the relatively open difference.

The perfect set theorem now follows the open-ball Cantor scheme in
`PerfectCantorScheme`: shrinking disjoint child closures, Cauchy branch
samples, unique limits, prefix continuity, and first-difference injectivity.
The same construction in closed perfect subspaces supplies the ingredient
used by Cantor--Bendixson uniqueness.

Kuratowski's isomorphism theorem now uses basic-open characteristic sequences,
the transfinite perfect kernel and Cantor scheme, and the explicit Borel
Schröder--Bernstein construction. The cardinality classification separates the
countable discrete case from that construction. `BorelCodeCardinality` serializes
the inductive codes into Baire space and bounds the number of decoded Borel sets;
singletons give the matching lower bound in the uncountable case. The final
comparison rules out the full power set of the reals as a standard Borel structure.
Finite Borel strictness uses the explicit universal-set diagonal and closed Cantor embedding.
Effros--Borel standardness follows both the pruned-tree realization and the ambient
closure construction in `EffrosBorelTrees` and `EffrosBorelCompact`.
The Cantor--Baire isomorphism follows the book's gap map
and countable-leftover patch in `CantorBaireBorelIsomorphism`.
The Kuratowski--Ryll-Nardzewski theorem is external and cited as such.
-/

namespace PolishSpaceBook

open Set TopologicalSpace
open scoped Cardinal

/-- The perfect kernel is an actual stable transfinite derivative stage. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem}]
-/
theorem cantorBendixsonDecomposition_exists
    {X : Type*} [TopologicalSpace X] [T1Space X] [SecondCountableTopology X]
    {F : Set X} (hF : IsClosed F) :
    ∃ P S : Set X,
      Perfect P ∧ S.Countable ∧ Disjoint P S ∧ F = P ∪ S := by
  obtain ⟨a, hP, hS, hdisj, heq⟩ := CantorBendixson.decomposition_exists hF
  exact ⟨CantorBendixson.stage F a, F \ CantorBendixson.stage F a, hP, hS, hdisj, heq⟩

/-- The perfect-set ingredient is isolated here: a nonempty relatively open
piece of a perfect Polish set contains a nonempty closed perfect subset,
so it cannot be countable. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Choose a closed neighborhood $V$ of $x$ disjoint from $Q$, and let $U$ be the interior of $V$.
    Then $U\cap P$ is nonempty and has no isolated points, so
    $$C=\Closure{U\cap P}$$
    is a nonempty perfect set. Indeed, a point of $C$ outside $U\cap P$ is a limit of points of $U\cap P$, and a
    point of $U\cap P$ is not isolated in $U\cap P$ and hence not isolated in $C$; so $C$ is closed with no isolated
    points. Moreover,
    $$C\IncludedIn V\cap P\IncludedIn\SetDifference{P}{Q}.$$
-/
theorem perfect_subset_of_countable_sdiff
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {P Q : Set X} (hP : Perfect P) (hQ : IsClosed Q) (hc : (P \ Q).Countable) :
    P ⊆ Q := by
  classical
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  intro x hx
  by_contra hxQ
  obtain ⟨V, hxV, hVc, hVQ⟩ := exists_mem_nhds_isClosed_subset (hQ.isOpen_compl.mem_nhds hxQ)
  obtain ⟨hC, hCne⟩ := hP.closure_nhds_inter x hx
    (mem_interior_iff_mem_nhds.mpr hxV) isOpen_interior
  have hsub : closure (interior V ∩ P) ⊆ P \ Q := by
    intro y hy
    refine ⟨closure_minimal inter_subset_right hP.closed hy, ?_⟩
    exact hVQ (closure_minimal (inter_subset_left.trans interior_subset) hVc hy)
  have hCc := hc.mono hsub
  obtain ⟨f, hfC, _, hf⟩ := PerfectCantorScheme.exists_injection_perfect hC hCne
  let g : (ℕ → Bool) → closure (interior V ∩ P) := fun b => ⟨f b, hfC (mem_range_self b)⟩
  have hg : Function.Injective g := fun b c h => hf (congrArg Subtype.val h)
  let := hCc.to_subtype
  exact cantor_space_not_countable hg.countable

/-- Uniqueness follows from the perfect-set theorem on the relatively open
countable difference, as in the book. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    The perfect set theorem in §{sec:perfect-set-theorem}, proved independently below by the Cantor-scheme
    construction, gives a copy of the Cantor space in $C$, contradicting countability.
    Hence $\SetDifference{P}{Q} = \emptyset$. Thus $P = Q$ and consequently $S = R$.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem}]
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Conversely, suppose $F = Q \cup R$, where $Q$ is perfect, $R$ is countable, and
    $Q\cap R=\emptyset$. We show $P \IncludedIn Q$.
    The difference $\SetDifference{P}{Q} \IncludedIn \SetDifference{F}{Q} = R$ is countable. Since $Q$ is closed,
    $\SetDifference{P}{Q}$ is open in $P$. Suppose it contains a point $x$.
-/
theorem cantorBendixsonDecomposition_unique
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {F P S Q R : Set X} (hP : Perfect P) (hS : S.Countable)
    (hPS : Disjoint P S) (hF : F = P ∪ S)
    (hQ : Perfect Q) (hR : R.Countable) (hQR : Disjoint Q R) (hF' : F = Q ∪ R) :
    P = Q ∧ S = R := by
  have hPQ : P ⊆ Q := perfect_subset_of_countable_sdiff hP hQ.closed (hR.mono (by
    rintro x ⟨hxP, hxQ⟩
    have hxF : x ∈ F := hF ▸ Or.inl hxP
    rw [hF'] at hxF
    exact hxF.resolve_left hxQ))
  have hQP : Q ⊆ P := perfect_subset_of_countable_sdiff hQ hP.closed (hS.mono (by
    rintro x ⟨hxQ, hxP⟩
    have hxF : x ∈ F := hF' ▸ Or.inl hxQ
    rw [hF] at hxF
    exact hxF.resolve_left hxP))
  have heq := hPQ.antisymm hQP
  refine ⟨heq, ?_⟩
  subst Q
  ext x
  constructor
  · intro hxS
    have hxF : x ∈ F := hF ▸ Or.inr hxS
    rw [hF'] at hxF
    exact hxF.resolve_left (fun hxP => Set.disjoint_left.mp hPS hxP hxS)
  · intro hxR
    have hxF : x ∈ F := hF' ▸ Or.inr hxR
    rw [hF] at hxF
    exact hxF.resolve_left (fun hxP => Set.disjoint_left.mp hQR hxP hxR)

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: statement
  kind: theorem
  title: perfect set theorem
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Finally, $h$ is a homeomorphism onto its image. The Cantor space $\CantorSpace$ is compact, and every metric space is
    Hausdorff; therefore a continuous injection from $\CantorSpace$ into $X$ is a homeomorphism onto its compact image.
-/
/-- A nonempty perfect Polish space contains a closed topological copy of
Cantor space. The closed embedding packages the homeomorphism onto its image. -/
theorem perfectSetTheorem_closedEmbedding
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [PerfectSpace X] [Nonempty X] :
    ∃ h : (ℕ → Bool) → X, Topology.IsClosedEmbedding h := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact ⟨PerfectCantorScheme.point, PerfectCantorScheme.point_closedEmbedding⟩

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    Define recursively
    $$X_0 := \SetDifference{X}{g(Y)}, \qquad X_{n+1} := (g \circ f)(X_n), \qquad X_\infty := \bigcup_{n \in \omega} X_n.$$
-/
/-- Iterates of the initial unmatched piece; their countable union selects the forward branch. -/
def borelSBStage {X Y : Type*} (f : X → Y) (g : Y → X) : ℕ → Set X
  | 0 => (range g)ᶜ
  | n + 1 => g '' (f '' borelSBStage f g n)

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Each $X_n$ is Borel: $X_0$ because $g(Y)$ is Borel by hypothesis; and inductively $X_{n+1}$ is the image of the Borel
    set $X_n$ under the Borel injection $g \circ f$, hence Borel by Lusin–Suslin. Therefore $X_\infty$ is Borel, and so is
    $\SetDifference{X}{X_\infty}$. By construction
    \begin{equation*}
    (g \circ f)(X_\infty) \;=\; \bigcup_{n \ge 1} X_n \;=\; \SetDifference{X_\infty}{X_0}. \tag{$\ast$}
    \end{equation*}
-/
theorem borelSBStage_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {g : Y → X} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (n : ℕ) : MeasurableSet (borelSBStage f g n) := by
  induction n with
  | zero => exact hg.measurableSet_range.compl
  | succ n ih => exact hg.measurableSet_image.mpr (hf.measurableSet_image.mpr ih)

theorem borelSBUnion_step {X Y : Type*} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) :
    g (f x) ∈ ⋃ n, borelSBStage f g n ↔ x ∈ ⋃ n, borelSBStage f g n := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    cases n with
    | zero => exact False.elim (hn ⟨f x, rfl⟩)
    | succ n =>
      obtain ⟨y, ⟨z, hz, hzy⟩, hyx⟩ := hn
      have : z = x := hf (hzy.trans (hg hyx))
      exact mem_iUnion.mpr ⟨n, this ▸ hz⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n + 1, ⟨f x, ⟨x, hn, rfl⟩, rfl⟩⟩

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    Define $h : X \to Y$ piecewise:
    $$h(x) =
    \begin{cases}
    f(x) & x \in X_\infty, \\[2pt]
    g^{-1}(x) & x \in \SetDifference{X}{X_\infty}.
    \end{cases}$$
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    This is well-defined: $\SetDifference{X}{X_\infty} \IncludedIn \SetDifference{X}{X_0} = g(Y)$, so $g^{-1}(x)$ exists,
    and $g$ is
    injective. Lusin–Suslin applied to $g$ shows that $g^{-1} : g(Y) \to Y$ is Borel; the restrictions $f|_{X_\infty}$ and
    $g^{-1}|_{\SetDifference{X}{X_\infty}}$ are Borel as restrictions of Borel maps to Borel sets. Hence $h$ is Borel.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    \emph{Injectivity.} Suppose $h(x_1) = h(x_2)$. The cases $x_1, x_2 \in X_\infty$ and $x_1, x_2 \in
    \SetDifference{X}{X_\infty}$
    reduce to injectivity of $f$ and $g^{-1}$ respectively. The mixed case has $x_1 \in X_\infty$, $x_2 \in
    \SetDifference{X}{X_\infty}$, with $f(x_1) = g^{-1}(x_2)$, hence $x_2 = (g \circ f)(x_1) \in
    \SetDifference{X_\infty}{X_0}$ by $(\ast)$ —
    contradicting $x_2 \notin X_\infty$.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    \emph{Surjectivity.} Let $y \in Y$. If $g(y) \in X_\infty$, then $g(y) \in g(Y)$ rules out $g(y) \in X_0$, so $g(y) \in
    X_n$ for some $n \ge 1$, i.e. $g(y) = (g \circ f)(x)$ for some $x \in X_{n-1} \IncludedIn X_\infty$; injectivity of $g$
    gives $y = f(x) = h(x)$. Otherwise $g(y) \in \SetDifference{X}{X_\infty}$, and $h(g(y)) = g^{-1}(g(y)) = y$.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    \emph{Borel inverse.} The bijectivity argument also identifies the inverse: $h^{-1}(y) = f^{-1}(y)$ when $y \in
    f(X_\infty)$, and $h^{-1}(y) = g(y)$ otherwise. Lusin–Suslin gives both that $f(X_\infty)$ is Borel and that $f^{-1} :
    f(X_\infty) \to X_\infty$ is Borel; the second branch is the restriction of the Borel map $g$. Hence $h^{-1}$ is Borel.
-/
/-- The two piecewise Borel maps are verified to be mutual inverses. -/
noncomputable def borelSBByStages {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] {f : X → Y} {g : Y → X}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) : X ≃ᵐ Y := by
  classical
  let A := ⋃ n, borelSBStage f g n
  have hA : MeasurableSet A := MeasurableSet.iUnion (borelSBStage_measurable hf hg)
  have hstep := borelSBUnion_step hf.injective hg.injective
  have hzero {x} (hx : x ∉ A) : x ∈ range g := by
    by_contra h
    exact hx (mem_iUnion.mpr ⟨0, h⟩)
  have hgback {x} (hx : x ∉ A) : g (hg.invFun x) = x := by
    obtain ⟨y, rfl⟩ := hzero hx
    rw [hg.leftInverse_invFun y]
  have hright {y} : g y ∈ A ↔ y ∈ f '' A := by
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      cases n with
      | zero => exact False.elim (hn ⟨y, rfl⟩)
      | succ n =>
        obtain ⟨z, ⟨x, hx, hxz⟩, hzy⟩ := hn
        exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, hxz.trans (hg.injective hzy)⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hstep x).mpr hx
  let h : X → Y := A.piecewise f hg.invFun
  let k : Y → X := (f '' A).piecewise hf.invFun g
  have hleft : Function.LeftInverse k h := by
    intro x
    by_cases hx : x ∈ A
    · have hy : f x ∈ f '' A := mem_image_of_mem f hx
      simp only [h, k, piecewise_eq_of_mem A _ _ hx, piecewise_eq_of_mem _ _ _ hy]
      exact hf.leftInverse_invFun x
    · have hy : hg.invFun x ∉ f '' A := by
        intro hy
        exact hx (hgback hx ▸ hright.mpr hy)
      simp only [h, k, piecewise_eq_of_notMem A _ _ hx,
        piecewise_eq_of_notMem _ _ _ hy]
      exact hgback hx
  have hrightinv : Function.RightInverse k h := by
    intro y
    by_cases hy : y ∈ f '' A
    · obtain ⟨x, hx, rfl⟩ := hy
      have hy : f x ∈ f '' A := mem_image_of_mem f hx
      simp only [k, piecewise_eq_of_mem _ _ _ hy, hf.leftInverse_invFun x,
        h, piecewise_eq_of_mem A _ _ hx]
    · have hx : g y ∉ A := fun hx => hy (hright.mp hx)
      simp only [k, h, piecewise_eq_of_notMem _ _ _ hy,
        piecewise_eq_of_notMem A _ _ hx]
      exact hg.leftInverse_invFun y
  exact { toFun := h
          invFun := k
          left_inv := hleft
          right_inv := hrightinv
          measurable_toFun := hf.measurable.piecewise hA hg.measurable_invFun
          measurable_invFun := hf.measurable_invFun.piecewise
            (hf.measurableSet_image.mpr hA) hg.measurable }
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: statement
  kind: theorem
  title: Borel Schröder–Bernstein
-/
/-- The measurable equivalence is constructed from the explicit iterated sets. -/
theorem borelSchroederBernstein_exists
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {g : Y → X}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) :
    Nonempty (X ≃ᵐ Y) := by
  classical
  by_cases hX : Nonempty X
  · let := hX
    let : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
    exact ⟨borelSBByStages hf hg⟩
  · let : IsEmpty X := not_nonempty_iff.mp hX
    let : IsEmpty Y := ⟨fun y => isEmptyElim (g y)⟩
    exact ⟨{ toEquiv := Equiv.equivOfIsEmpty X Y
             measurable_toFun := measurable_of_empty _
             measurable_invFun := measurable_of_empty _ }⟩

/-- Record membership in each member of a sequence of open basic sets. -/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    (i) \emph{Code points of $X$ by Cantor reals.} Fix a countable base $\IndexedFamily{U_n}{n\in\NN}$ for $X$ and define
    $$
    \varphi:X\to\CantorSpace,
    \qquad
    \varphi(x)_n=\mathbf{1}[x\in U_n].
    $$
-/
noncomputable def basisCode {X : Type*} (U : ℕ → Set X) (x : X) : cantor_space :=
  fun n => @decide (x ∈ U n) (Classical.propDecidable _)

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    For each $n\in\NN$,
    $$\varphi^{-1}(\{a\in\CantorSpace:a_n=1\})=U_n.$$
    Thus $\varphi$ is \termuseas{Borel-measurable map}{Borel measurable}, since the coordinate cylinders generate the
    Borel $\sigma$-algebra of $\CantorSpace$.
-/
theorem basisCode_measurable {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) : Measurable (basisCode U) := by
  apply Measurable.of_eval
  intro n
  apply measurable_to_bool
  have heq : (fun x => basisCode U x n) ⁻¹' {true} = U n := by
    ext x
    simp [basisCode]
  rw [heq]
  exact (hU n).measurableSet

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    If $x\ne y$, choose a basic open set with
    $x\in U_n\IncludedIn\SetDifference{X}{\{y\}}$. Then $\varphi(x)_n=1$ and $\varphi(y)_n=0$, proving injectivity.
-/
theorem basisCode_injective {X : Type*} [TopologicalSpace X] [T1Space X]
    (U : ℕ → Set X) (hU : IsTopologicalBasis (range U)) :
    Function.Injective (basisCode U) := by
  intro x y h
  by_contra hxy
  have hx : x ∈ ({y} : Set X)ᶜ := by simpa using hxy
  obtain ⟨V, ⟨n, rfl⟩, hxV, hV⟩ := hU.exists_subset_of_mem_open hx isClosed_singleton.isOpen_compl
  have hmem : x ∈ U n ↔ y ∈ U n := by
    simpa [basisCode] using congrFun h n
  exact hV (hmem.mp hxV) (by simp)

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    By the Lusin--Suslin theorem of §{sec:lusin-souslin-theorem}, $\varphi(A)$ is Borel in $\CantorSpace$ for every
    Borel set $A\IncludedIn X$. In particular, $\varphi(X)$ is Borel, and the inverse from this image to $X$ is Borel.
-/
theorem exists_basisCode_measurableEmbedding {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] :
    ∃ U : ℕ → Set X, IsTopologicalBasis (range U) ∧ MeasurableEmbedding (basisCode U) := by
  obtain ⟨U, hU⟩ := exists_seq_basis X
  exact ⟨U, hU, (basisCode_measurable U (fun n => hU.isOpen (mem_range_self n))).measurableEmbedding
    (basisCode_injective U hU)⟩

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    (ii) \emph{Find a Cantor copy inside $X$.} Apply the
    \termuseas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem} to $X$ as a closed subset of itself. The
    \termuse{scattered part} is countable, so the \termuse{perfect kernel} is nonempty because $X$ is uncountable. By
    \termuseas{perfect set theorem}{the perfect set theorem} in §{sec:perfect-set-theorem}, this nonempty perfect Polish
    subspace contains a homeomorphic copy $P$ of $\CantorSpace$. Since $P$ is compact and $X$ is Hausdorff, $P$ is closed in
    $X$, hence Borel. The homeomorphism $\psi:\CantorSpace\to P\IncludedIn X$ is therefore a Borel injection with Borel
    image.
-/
theorem uncountable_cantor_closedEmbedding {X : Type*} [TopologicalSpace X]
    [PolishSpace X] (hX : ¬ Countable X) :
    ∃ g : cantor_space → X, Topology.IsClosedEmbedding g := by
  obtain ⟨P, S, hP, hS, _, hcover⟩ := cantorBendixsonDecomposition_exists (X := X) isClosed_univ
  have hne : P.Nonempty := by
    by_contra h
    have hp : P = ∅ := not_nonempty_iff_eq_empty.mp h
    have hs : S = univ := by simpa [hp] using hcover.symm
    exact hX (countable_univ_iff.mp (hs ▸ hS))
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨g, _, hg, hinj⟩ := PerfectCantorScheme.exists_injection_perfect hP hne
  exact ⟨g, hg.isClosedEmbedding hinj⟩

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    The Borel Schröder--Bernstein theorem below then patches the parts not already matched by these
    embeddings, producing a Borel bijection $X\to\CantorSpace$ with Borel inverse. This is the abstract version of the
    explicit countable-leftover patch in the Cantor--Baire example.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    It suffices to prove every uncountable Polish space $X$ is Borel-isomorphic to the Cantor space
    $\CantorSpace$. The argument abstracts the Cantor--Baire construction in §{sec:cantor-baire-borel-isomorphism}. There, one large Borel piece was matched by
    a concrete homeomorphism and the countable leftovers were patched by hand. For an arbitrary uncountable Polish space the
    pieces need not be so explicit, but two Borel embeddings give the same structure, and Borel Schröder--Bernstein performs
    the bookkeeping.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Thus we have Borel injections
    $$
    X \overset{\varphi}{\longrightarrow} \CantorSpace,
    \qquad
    \CantorSpace \overset{\psi}{\longrightarrow} X
    $$
    with Borel images.
-/
theorem kuratowskiToCantor_exists {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (hX : ¬ Countable X) :
    Nonempty (X ≃ᵐ cantor_space) := by
  obtain ⟨U, _, hf⟩ := exists_basisCode_measurableEmbedding (X := X)
  obtain ⟨g, hg⟩ := uncountable_cantor_closedEmbedding hX
  exact borelSchroederBernstein_exists hf hg.measurableEmbedding

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: statement
  kind: theorem
  title: Kuratowski's isomorphism theorem
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    \emph{Uncountable case.} \termuseas{Kuratowski's isomorphism theorem}{Kuratowski's theorem} in
    §{sec:kuratowski-isomorphism} gives a Borel isomorphism between any two uncountable Polish spaces; the same isomorphism
    witnesses Borel isomorphism between any two uncountable standard Borel spaces, since each is presented by some
    uncountable Polish topology.
-/
/-- Any two uncountable standard Borel spaces are measurably equivalent. This
applies in particular to Polish spaces equipped with their Borel sigma
algebras. -/
theorem kuratowskiIsomorphism_exists
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (hX : ¬ Countable X) (hY : ¬ Countable Y) :
    Nonempty (X ≃ᵐ Y) := by
  let := upgradeStandardBorel X
  let := upgradeStandardBorel Y
  obtain ⟨eX⟩ := kuratowskiToCantor_exists hX
  obtain ⟨eY⟩ := kuratowskiToCantor_exists hY
  exact ⟨eX.trans eY.symm⟩

/-- The book's standard Borel predicate, represented by mathlib's canonical
class whose field is a compatible Polish topology. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: statement
  excerpt: |
    \begin{definition*} \emph{A measurable space $(X, \mathcal B)$ is a \termdefine{standard Borel space} [@Kechris1995,
-/
def IsStandardBorelSpace (X : Type*) [MeasurableSpace X] : Prop :=
  StandardBorelSpace X

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Consequently, every bijection between countable standard Borel spaces, as well as its inverse, is Borel.
    A finite space with $n$ points is therefore Borel-isomorphic to $(n,\PowerSet{n})$, including $n=0$;
    a countably infinite space is Borel-isomorphic to $(\NN,\PowerSet{\NN})$.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Kuratowski's theorem and the countable-cardinality cases together yield a complete classification of the measurable
    spaces that arise from Polish topologies.
-/
/-- Standard Borel spaces are Borel-isomorphic exactly when their underlying
types have the same cardinality. -/
theorem standardBorelClassificationByCardinality
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] :
    Nonempty (X ≃ᵐ Y) ↔ Nonempty (X ≃ Y) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEquiv⟩
  · rintro ⟨e⟩
    by_cases hX : Countable X
    · let := hX
      let : Countable Y := e.symm.injective.countable
      exact ⟨⟨e, measurable_of_countable _, measurable_of_countable _⟩⟩
    · have hY : ¬ Countable Y := fun hY => hX (by let := hY; exact e.injective.countable)
      exact kuratowskiIsomorphism_exists hX hY

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: proof
  excerpt: |
    \emph{Countable case.} Every subset of a countable Polish space $X$ is a countable union of singletons.
    Singletons are closed because $X$ is $T_1$, hence Borel, so $\mathcal B(X) = \PowerSet{X}$.
-/
theorem countable_standardBorel_all_sets {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] [Countable X] (s : Set X) : MeasurableSet s :=
  s.to_countable.measurableSet

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: statement
  kind: theorem
  title: Classification of standard Borel spaces
-/
theorem standardBorel_representatives {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] :
    (∃ n : ℕ, Nonempty (X ≃ᵐ Fin n)) ∨ Nonempty (X ≃ᵐ ℕ) ∨ Nonempty (X ≃ᵐ ℝ) := by
  classical
  by_cases hX : Countable X
  · let := hX
    by_cases hf : Finite X
    · let := Fintype.ofFinite X
      exact Or.inl ⟨Fintype.card X,
        standardBorelClassificationByCardinality.mpr ⟨Fintype.equivFin X⟩⟩
    · let : Infinite X := not_finite_iff_infinite.mp hf
      exact Or.inr (Or.inl (standardBorelClassificationByCardinality.mpr nonempty_equiv_of_countable))
  · exact Or.inr (Or.inr (kuratowskiIsomorphism_exists hX not_countable))

theorem cantorSpace_cardinal : Cardinal.mk cantor_space = 𝔠 := by
  simp [cantor_space, Cardinal.two_power_aleph0]

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Indeed, an uncountable closed set has a nonempty \termuse{perfect kernel} by the
    \termuseas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem}, and the \termuse{perfect set theorem} embeds
    $\CantorSpace$ into that kernel. Conversely, the base-indicator map used in
    §{sec:kuratowski-isomorphism} injects every Polish space into $\CantorSpace$.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    If $X$ is uncountable, the cardinality dichotomy gives $|X|=2^{\alephNull}$.
-/
theorem uncountable_polish_cardinal {X : Type} [TopologicalSpace X]
    [PolishSpace X] (hX : ¬ Countable X) : Cardinal.mk X = 𝔠 := by
  obtain ⟨U, hU⟩ := exists_seq_basis X
  have hupper := Cardinal.mk_le_of_injective (basisCode_injective U hU)
  obtain ⟨g, hg⟩ := uncountable_cantor_closedEmbedding hX
  have hlower := Cardinal.mk_le_of_injective hg.injective
  rw [cantorSpace_cardinal] at hupper hlower
  exact le_antisymm hupper hlower

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Every closed subset of a Polish space is either countable or has cardinality exactly $2^{\alephNull}$.
-/
theorem closedSet_cardinality_dichotomy {X : Type} [TopologicalSpace X]
    [PolishSpace X] {F : Set X} (hF : IsClosed F) : F.Countable ∨ Cardinal.mk F = 𝔠 := by
  classical
  by_cases hc : F.Countable
  · exact Or.inl hc
  · let : PolishSpace F := hF.polishSpace
    exact Or.inr (uncountable_polish_cardinal (fun h => hc (by let := h; exact Set.to_countable F)))

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    The map $x\mapsto\{x\}$ injects $X$ into $\mathcal B(X)$, since distinct points give distinct closed singletons.
-/
theorem cardinal_le_borelSets {X : Type} [MeasurableSpace X] [MeasurableSingletonClass X] :
    #X ≤ #{A : Set X // MeasurableSet A} := by
  let f : X → {A : Set X // MeasurableSet A} := fun x => ⟨{x}, measurableSet_singleton x⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro x y h
  have hsets : ({x} : Set X) = {y} := congrArg Subtype.val h
  simpa using hsets

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Together with the upper bound, this yields
    $$2^{\alephNull}=|X|\le|\mathcal B(X)|\le2^{\alephNull},\qquad |\mathcal B(X)|=2^{\alephNull}.$$
-/
theorem uncountable_borelSets_cardinal {X : Type} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (hX : ¬ Countable X) :
    #{A : Set X // MeasurableSet A} = 𝔠 := by
  apply le_antisymm borelSets_cardinal_le_continuum
  rw [← uncountable_polish_cardinal hX]
  exact cardinal_le_borelSets

theorem real_powerset_cardinal : #(Set ℝ) = 2 ^ 𝔠 := by
  rw [Cardinal.mk_set, Cardinal.mk_real]

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    In contrast, Cantor's theorem gives
    $$|\PowerSet{\R}|=2^{2^{\alephNull}}>2^{\alephNull}.$$
-/
theorem continuum_lt_real_powerset : 𝔠 < #(Set ℝ) := by
  rw [real_powerset_cardinal]
  exact Cardinal.cantor _

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Thus $(\R,\PowerSet{\R})$ is *not* a standard Borel space. Any Polish topology on the underlying set $\R$ has only
    $2^{\alephNull}$ Borel sets, so none can generate the full power set. The standard Borel hypothesis therefore
    restricts the $\sigma$-algebra, not merely the cardinality of the underlying set.
-/
theorem real_powerset_not_standardBorel : ¬ @StandardBorelSpace ℝ ⊤ := by
  intro h
  let : MeasurableSpace ℝ := ⊤
  let : StandardBorelSpace ℝ := h
  let := upgradeStandardBorel ℝ
  have hu := borelSets_cardinal_le_continuum (X := ℝ)
  let f : Set ℝ → {A : Set ℝ // MeasurableSet A} := fun A => ⟨A, by trivial⟩
  have hf : Function.Injective f := fun A B hAB => congrArg Subtype.val hAB
  have hc := (Cardinal.mk_le_of_injective hf).trans hu
  exact (not_le_of_gt continuum_lt_real_powerset) hc

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The Cantor--Bendixson theorem and the perfect set theorem give a closed embedding
    $g:\CantorSpace\to X$. Induction on the Borel level shows that every $\bSigma^0_n$ set $A$ in $\CantorSpace$
    has the form $A=g^{-1}(B)$ for some $\bSigma^0_n$ set $B$ in $X$, and likewise for $\bPi^0_n$.
    At the first level this is the definition of the induced topology. The induction step uses
    $$
    \begin{aligned}
    g^{-1}(\SetDifference{X}{B})&=\SetDifference{\CantorSpace}{g^{-1}(B)},\\
    g^{-1}\Bigl(\bigcup_k B_k\Bigr)&=\bigcup_k g^{-1}(B_k).
    \end{aligned}
    $$
    By §{sec:finite-borel-universal}, choose $D\in\bPi^0_n$ in $\CantorSpace$ with $D\notin\bSigma^0_n$.
    Lift it to a set $T\in\bPi^0_n$ in $X$ with $g^{-1}(T)=D$. If $T$ belonged to $\bSigma^0_n$, continuity of $g$
    would put $D$ in the same class, a contradiction. Thus the two classes on $X$ are distinct.
    \end{proof}
-/
/-- Lift the Cantor anti-diagonal along the closed embedding constructed from the
Cantor–Bendixson perfect kernel. Continuous preimages preserve the same level. -/
theorem finite_borel_diagonal_polish {X : Type*} [TopologicalSpace X] [PolishSpace X]
    (hX : ¬ Countable X) (n : ℕ) :
    ∃ D : Set X, D ∈ borelPi (↑n + 1) ∧ D ∉ borelSigma (↑n + 1) := by
  obtain ⟨g, hg⟩ := uncountable_cantor_closedEmbedding hX
  obtain ⟨D, hD, hDn⟩ := finite_borel_strictness_cantor n
  obtain ⟨T, hT, hTD⟩ := borelPi_lift_inducing g hg.isEmbedding.isInducing _ hD
  refine ⟨T, hT, fun h => hDn ?_⟩
  rw [← hTD]
  exact borelSigma_preimage g hg.continuous _ h

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: statement
  kind: theorem
  title: Finite Borel strictness
-/
/-- Every positive finite Borel level separates the additive and multiplicative
classes on any uncountable Polish space. -/
theorem finite_borel_strictness_polish {X : Type*} [TopologicalSpace X] [PolishSpace X]
    (hX : ¬ Countable X) (n : ℕ) (hn : 1 ≤ n) :
    borelSigma (Y := X) (n : Ordinal) ≠ borelPi (n : Ordinal) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨D, hD, hDn⟩ := finite_borel_diagonal_polish hX m
  rw [Nat.cast_succ]
  intro h
  exact hDn (h.symm ▸ hD)

end PolishSpaceBook
