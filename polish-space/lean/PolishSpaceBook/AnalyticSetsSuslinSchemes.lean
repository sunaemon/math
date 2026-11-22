module

public import PolishSpaceBook.AnalyticBorelMaps
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Analytic sets and Suslin schemes

Formalization targets for
`polish-space/src/polish-space-book/analytic-sets-suslin-schemes.md`.

Formalized here are the continuous-image definition of analytic sets, the
closed- and Borel-projection characterizations over Baire space, closure under
Borel images, Suslin's theorem, the Suslin operation and its branch-membership
form, the degenerate countable-union scheme, and the proof that a closed scheme
produces an analytic set.

`RegularSuslinSchemes` completes the recursive clopen partition, simultaneous
source/image diameter bounds, and branch-convergence proof of the regular
representation theorem. The cited non-Borelness of ill-founded trees is an
external theorem; its transport to arbitrary uncountable Polish spaces is a
completed construction in `AnalyticNonBorelTransport`. `AnalyticBorelMaps` supplies
the clopen-refinement arguments and the book's Baire-surjection construction.
The separation implication still uses mathlib's analytic separation theorem;
matching the next chapter's rank proof remains a separate formalization task.
-/

namespace PolishSpaceBook

noncomputable section

universe u v

open Function MeasureTheory Set Topology

section AnalyticSets

variable {X : Type u} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    A subset $A \IncludedIn X$ of a Polish space is \termdefineas{analytic set}{analytic} ($\bSigma^1_1$) if it is the
    continuous image of a Polish space.
-/
/-- The book's continuous-image definition of an analytic set. -/
theorem analyticSet_iff_continuous_image_polish (A : Set X) :
    AnalyticSet A ↔
      ∃ (Z : Type) (tZ : TopologicalSpace Z) (_ : @PolishSpace Z tZ)
        (f : Z → X), @Continuous Z X tZ _ f ∧ range f = A := by
  constructor
  · intro hA
    rw [AnalyticSet] at hA
    rcases hA with rfl | ⟨f, hf, hr⟩
    · exact ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, range_eq_empty _⟩
    · exact ⟨baire_space, inferInstance, inferInstance, f, hf, hr⟩
  · rintro ⟨Z, tZ, hZ, f, hf, rfl⟩
    exact @analyticSet_range_via_baire_surjection Z X tZ hZ _ f hf

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Complements of analytic sets are \termdefineas{coanalytic set}{coanalytic} ($\bPi^1_1$).
-/
/-- A set is coanalytic when its complement is analytic. -/
def CoanalyticSet (A : Set X) : Prop :=
  AnalyticSet Aᶜ

variable [PolishSpace X]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: proposition
  title: Closed-projection theorem
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Suppose first that $A$ is analytic. If $A=\emptyset$, use the empty closed subset of $X\times
    \BaireSpace$. Otherwise, write $A=g(Z)$ for a nonempty Polish space $Z$ and a continuous map $g:Z\to X$. By the
    universal continuous-surjection theorem of §{sec:universal-continuous-surjection}, there is a continuous surjection
    $q:\BaireSpace\to Z$. The graph
    $$
    C:=\{\Pair{g(q(p))}{p}:p\in\BaireSpace\}
    $$
    is closed in $X\times\BaireSpace$, because $X$ is Hausdorff and $g\circ q$ is continuous, and its projection to $X$ is
    $A$.

    Conversely, if $C\IncludedIn X\times\BaireSpace$ is closed, then $C$ is Polish by the closed-subspace result of
    §{sec:polish-key-properties}. The coordinate projection $C\to X$ is continuous, so its image is analytic.
    \end{proof}
-/
/-- Analytic subsets of a Polish space are exactly projections of closed
subsets of the product with Baire space. -/
theorem analyticSet_iff_closed_baire_projection (A : Set X) :
    AnalyticSet A ↔
      ∃ C : Set (X × baire_space), IsClosed C ∧ Prod.fst '' C = A := by
  constructor
  · intro hA
    obtain ⟨Z, tZ, hZ, g, hg, rfl⟩ := (analyticSet_iff_continuous_image_polish A).mp hA
    let := tZ
    let := hZ
    cases isEmpty_or_nonempty Z
    · exact ⟨∅, isClosed_empty, by simp only [image_empty, range_eq_empty]⟩
    · obtain ⟨q, hq, hsurj⟩ := exists_baire_continuous_surjection Z
      let f := g ∘ q
      have hf : Continuous f := hg.comp hq
      refine ⟨{z | z.1 = f z.2},
        isClosed_eq continuous_fst (hf.comp continuous_snd), ?_⟩
      rw [← hsurj.range_comp g]
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz.symm⟩
      · rintro ⟨p, rfl⟩
        exact ⟨(f p, p), rfl, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    let : PolishSpace C := hC.polishSpace
    have hr : range (fun z : C => z.val.1) = Prod.fst '' C := by ext x; simp
    rw [← hr]
    exact analyticSet_range_via_baire_surjection (continuous_fst.comp continuous_subtype_val)

variable [MeasurableSpace X] [BorelSpace X]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: theorem
  title: Suslin
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The following \termforward{Suslin's theorem} identifies the first projective ambiguity class with the Borel sets.
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Equivalently,
    $$\bDelta^1_1(X) \;:=\; \bSigma^1_1(X) \cap \bPi^1_1(X) \;=\; \mathcal B(X).$$
    Thus the first projective ambiguity class is not a new class at all: it is exactly the Borel $\sigma$-algebra.
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The equivalence of (2) and (3) is just the definition of coanalytic: $A$ is coanalytic exactly when
    $\SetDifference{X}{A}$ is analytic.

    Suppose first that $A$ is Borel. By \termuse{Kuratowski's refinement theorem} in §{sec:polish-topology-refinement},
    refine the topology of $X$ to a Polish topology $\tau'$ with the same Borel sets and with $A$ clopen. The identity map
    $$
    (X,\tau')\longrightarrow (X,\tau)
    $$
    is continuous because $\tau'$ refines $\tau$. Since $A$ is clopen in $(X,\tau')$, it is Polish in the subspace topology
    by the closed-subspace result of §{sec:polish-key-properties}. The identity map sends this Polish space continuously onto
    $A$ as a subset of the original space. Thus $A$ is analytic. The same argument applied to the Borel set
    $\SetDifference{X}{A}$ shows that $\SetDifference{X}{A}$ is analytic.

    Conversely, suppose that both $A$ and $\SetDifference{X}{A}$ are analytic. By
    \termforward{Lusin separation theorem}, proved in
    §{sec:lusin-separation} of the next chapter, there is a Borel set $B\IncludedIn X$ such that
    $$A\IncludedIn B\IncludedIn \SetDifference{X}{(\SetDifference{X}{A})}=A.$$
    Hence $B=A$, so $A$ is Borel.
    \end{proof}
-/
/-- Suslin's theorem: a set is Borel exactly when it and its complement are
analytic. -/
theorem suslin_theorem {A : Set X} :
    MeasurableSet A ↔ AnalyticSet A ∧ AnalyticSet Aᶜ := by
  constructor
  · intro hA
    exact ⟨analyticSet_of_borel_via_refinement hA, analyticSet_of_borel_via_refinement hA.compl⟩
  · rintro ⟨hA, hAc⟩
    obtain ⟨B, hAB, hdisj, hB⟩ := hA.measurablySeparable hAc disjoint_compl_right
    have hBA : B ⊆ A := by
      intro x hx
      by_contra hxA
      exact Set.disjoint_left.mp hdisj hxA hx
    exact (Set.Subset.antisymm hAB hBA) ▸ hB

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: proposition
  title: Further characterizations of analytic sets
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The \termuse{closed-projection characterization of analytic sets} gives (1) $\Rightarrow$ (2).
    For (2) $\Rightarrow$ (1), the Borel-to-analytic implication of \termuse{Suslin's theorem} makes the Borel subset of
    $X\times Y$ analytic, and continuous images of analytic sets are analytic. Applying this to the coordinate projection
    gives $A$.

-/
/-- The Borel-projection characterization can use Baire space as the second
factor. -/
theorem analyticSet_iff_borel_baire_projection (A : Set X) :
    AnalyticSet A ↔
      ∃ C : Set (X × baire_space), MeasurableSet C ∧ Prod.fst '' C = A := by
  constructor
  · intro hA
    obtain ⟨C, hC, hproj⟩ :=
      (analyticSet_iff_closed_baire_projection A).1 hA
    exact ⟨C, hC.measurableSet, hproj⟩
  · rintro ⟨C, hC, rfl⟩
    exact (analyticSet_of_borel_via_refinement hC).image_of_continuous continuous_fst

variable {Y : Type v} [TopologicalSpace Y] [PolishSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The same closed subset of $X\times\BaireSpace$, viewed as a Borel domain for the coordinate projection, proves (1)
    $\Rightarrow$ (3). Conversely, suppose $A=f(D)$, where $D$ is Borel in a Polish space $Y$ and $f:Y\to X$ is Borel.
    Choose a countable base $\Sequence{V_n}{n\in\omega}$ of $X$ and apply \termuse{Kuratowski's refinement theorem} to the
    family
    $$E_0:=D,\qquad E_{n+1}:=f^{-1}(V_n)\quad(n\in\omega).$$
    Every $E_n$ is Borel. In the resulting Borel-preserving Polish topology on $Y$, all the $E_n$ are clopen.
    Thus $D$ is Polish, and $f$ is continuous because the inverse image of every basic open set is open.
    The restriction $f|_D$ is continuous and has image $A$, so $A$ is analytic.
    \end{proof}
-/
/-- A Borel image of a Borel subset of a Polish space is analytic. -/
theorem analyticSet_image_of_borel {B : Set Y} {f : Y → X}
    (hB : MeasurableSet B) (hf : Measurable f) :
    AnalyticSet (f '' B) :=
  analyticSet_borel_image_via_refinement hB hf

end AnalyticSets

section SuslinOperation

variable {X : Type u}

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Let $\IndexedFamily{A_s}{s\in\finseq{\omega}}$ be a family of subsets of a space $X$. The \termuse{Suslin operation}
    $\mathcal A$
    sends
    this family to
    $$
    \mathcal A(A_s)
    \;:=\;
    \bigcup_{p\in\BaireSpace}\ \bigcap_{n\in\omega} A_{\restrict{p}{n}}.
    $$
-/
/-- The Suslin operation on a tree-indexed family of sets. -/
def suslinOperation (A : finseq ℕ → Set X) : Set X :=
  ⋃ p : baire_space, ⋂ n : ℕ, A (seqPrefix p n)

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Thus
    $$
    x\in\mathcal A(A_s)
    \quad\Longleftrightarrow\quad
    \exists p\in\BaireSpace\ \forall n\; x\in A_{\restrict{p}{n}}.
    $$
-/
theorem mem_suslinOperation {A : finseq ℕ → Set X} {x : X} :
    x ∈ suslinOperation A ↔
      ∃ p : baire_space, ∀ n : ℕ, x ∈ A (seqPrefix p n) := by
  simp [suslinOperation]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The sequence $p$ is a witness branch. A family $\{A_s\}$ used in this way is called a \termdefine{Suslin scheme}. It is
    \termdefineas{monotone Suslin scheme}{monotone} if
    $$A_{s\concat(k)}\IncludedIn A_s\qquad(s\in\finseq{\omega},\ k\in\omega),$$
-/
/-- Monotonicity down the tree for a Suslin scheme. -/
def IsMonotoneSuslinScheme (A : finseq ℕ → Set X) : Prop :=
  ∀ s k, A (concat s [k]) ⊆ A s

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    and, in a metric space $(X,d)$, a monotone scheme is \termdefineas{regular Suslin scheme}{regular} if additionally the
    sets are closed and
    $$\MetricDiameter{d}{A_s}\le 2^{-|s|}.$$
-/
/-- A regular Suslin scheme is monotone, closed at every node, and has the
prescribed geometric diameter bound. The extended diameter keeps the predicate
faithful even for an a priori unbounded set. -/
def IsRegularSuslinScheme [MetricSpace X] (A : finseq ℕ → Set X) : Prop :=
  IsMonotoneSuslinScheme A ∧
    (∀ s, IsClosed (A s)) ∧
      ∀ s, Metric.ediam (A s) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ s.length)

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The operation contains ordinary countable unions as a degenerate case: if $A_\emptyset=X$, $A_{(n)}=B_n$, and
    $A_s=A_{\restrict{s}{1}}$ for all nonempty $s$, then
    $$\mathcal A(A_s)=\bigcup_n B_n.$$
-/
/-- A scheme constant below its first coordinate realizes an ordinary
countable union. -/
theorem suslinOperation_eq_iUnion_of_degenerate
    (A : finseq ℕ → Set X) (B : ℕ → Set X)
    (hroot : A [] = univ)
    (hfirst : ∀ n, A [n] = B n)
    (htail : ∀ s, s ≠ [] → A s = A (s.take 1)) :
    suslinOperation A = ⋃ n, B n := by
  ext x
  constructor
  · rw [mem_suslinOperation]
    rintro ⟨p, hp⟩
    refine mem_iUnion.2 ⟨p 0, ?_⟩
    simpa [seqPrefix, hfirst] using hp 1
  · rw [mem_iUnion]
    rintro ⟨k, hk⟩
    rw [mem_suslinOperation]
    refine ⟨fun _ ↦ k, ?_⟩
    intro n
    cases n with
    | zero => simp [seqPrefix, hroot]
    | succ n =>
        rw [htail _ (by simp [seqPrefix])]
        simpa [seqPrefix, hfirst] using hk

section ClosedSchemes

variable [TopologicalSpace X]

/-- The closed set of branch-point pairs associated with a closed scheme. -/
def closedSchemeWitness (F : finseq ℕ → Set X) : Set (baire_space × X) :=
  {z | ∀ n : ℕ, z.2 ∈ F (seqPrefix z.1 n)}

/-- The constraint imposed by a closed scheme at one fixed level. -/
def schemeLevel (F : finseq ℕ → Set X) (n : ℕ) : Set (baire_space × X) :=
  {z | z.2 ∈ F (seqPrefix z.1 n)}

theorem isClosed_schemeLevel {F : finseq ℕ → Set X}
    (hF : ∀ s, IsClosed (F s)) (n : ℕ) :
    IsClosed (schemeLevel F n) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  have hz' : z.2 ∉ F (seqPrefix z.1 n) := by
    simpa [schemeLevel] using hz
  let s := seqPrefix z.1 n
  let U : Set (baire_space × X) := cyl s ×ˢ (F s)ᶜ
  have hUopen : IsOpen U :=
    (baire_cyl_clopen s).isOpen.prod (hF s).isOpen_compl
  have hzU : z ∈ U := by
    exact ⟨mem_cyl_seqPrefix z.1 n, by simpa [s] using hz'⟩
  refine Filter.mem_of_superset (hUopen.mem_nhds hzU) ?_
  rintro y ⟨hycyl, hyF⟩
  have hpref : seqPrefix y.1 n = s := by
    simpa [s, seqPrefix_length] using seqPrefix_eq_of_mem_cyl hycyl
  simp only [mem_compl_iff, schemeLevel, mem_ofPred_eq]
  intro hy
  change y.2 ∈ F (seqPrefix y.1 n) at hy
  rw [hpref] at hy
  exact hyF hy

theorem isClosed_closedSchemeWitness {F : finseq ℕ → Set X}
    (hF : ∀ s, IsClosed (F s)) :
    IsClosed (closedSchemeWitness F) := by
  rw [show closedSchemeWitness F = ⋂ n : ℕ, schemeLevel F n by
    ext z
    simp [closedSchemeWitness, schemeLevel]]
  exact isClosed_iInter (isClosed_schemeLevel hF)

omit [TopologicalSpace X] in
theorem snd_image_closedSchemeWitness (F : finseq ℕ → Set X) :
    Prod.snd '' closedSchemeWitness F = suslinOperation F := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_suslinOperation.2 ⟨z.1, hz⟩
  · intro hx
    obtain ⟨p, hp⟩ := mem_suslinOperation.1 hx
    exact ⟨(p, x), hp, rfl⟩

variable [PolishSpace X]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: proposition
  title: Closed schemes produce analytic sets
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Consider
    $$
    C
    :=
    \{(p,x)\in\BaireSpace\times X:\forall n,\ x\in F_{\restrict{p}{n}}\}.
    $$
    For fixed $n$, the condition $x\in F_{\restrict{p}{n}}$ defines the closed set
    $$
    \bigcup_{|s|=n}\cyl{s}\times F_s.
    $$
    It is closed because its complement is
    $$
    \bigcup_{|s|=n}\cyl{s}\times (\SetDifference{X}{F_s}),
    $$
    which is open. Hence $C$ is closed as a countable intersection of closed sets. Its projection to $X$ is exactly
    $\mathcal A(F_s)$, so $\mathcal A(F_s)$ is analytic.
    \end{proof}
-/
/-- The Suslin operation applied to a closed scheme produces an analytic set. -/
theorem analyticSet_suslinOperation_of_isClosed
    {F : finseq ℕ → Set X} (hF : ∀ s, IsClosed (F s)) :
    AnalyticSet (suslinOperation F) := by
  rw [← snd_image_closedSchemeWitness F]
  exact (isClosed_closedSchemeWitness hF).analyticSet.image_of_continuous continuous_snd

end ClosedSchemes

end SuslinOperation

end

end PolishSpaceBook
