module

public import PolishSpaceBook.InternalFiniteMeasureCovers
public import PolishSpaceBook.CountablyAdditiveCutGraphs

@[expose] public section

/-! # Conull covers of dense representative families, using finite approximations -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas
universe u

namespace FiniteAdditiveCutGraph
variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

/-- Closure under unions of whole internal families follows from the disjoint-family axiom. -/
lemma internal_union_domain {M Y : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hca : h.CountablyAdditiveOn M) (hYM : Y ∈ M) (hY : Y ∈ D)
    (U : ℕ → ZFSet.{u}) (hUG : sequenceGraph U ∈ M)
    (hU : ∀ n, U n ∈ D) (hUY : ∀ n, U n ⊆ Y) : sequenceUnion U ∈ D := by
  let P := partialUnion U
  have hPG := partialUnion_sequence_mem hM hinf hpair hunion hsep hrep U hUG
  have hPM (n : ℕ) : P n ∈ M := sequence_term_mem hM hunion P hPG n
  let W (n : ℕ) := Y.sep (fun x => x ∉ P n)
  have hWG := sequenceRelativeComplement_mem hM hinf hpair hunion hsep hrep ⟨Y, hYM⟩
    (fun n => ⟨P n, hPM n⟩) hPG
  have hW (n : ℕ) : W n ∈ D := by
    have he : W n = Y \ P n := by ext x; simp [W]
    rw [he]
    exact h.diff_mem Y hY _ (h.partialUnion_domain U hU n)
  have hanti : Antitone (fun n => (W n : Set ZFSet)) := by
    intro m n hmn x hx
    obtain ⟨hxY, hxP⟩ := ZFSet.mem_sep.mp hx
    exact ZFSet.mem_sep.mpr ⟨hxY, fun hx => hxP (partialUnion_mono U hmn hx)⟩
  have hI := (h.continuity_from_above hM hinf hpair hunion hsep hrep hca W hWG hW hanti).1
  have he : Y \ sequenceIntersection W = sequenceUnion U := by
    ext x
    simp only [ZFSet.mem_sdiff, mem_sequenceIntersection]
    constructor
    · rintro ⟨hxY, hx⟩
      by_contra hn
      apply hx
      intro n
      exact ZFSet.mem_sep.mpr ⟨hxY, fun hp =>
        hn ((mem_sequenceUnion_iff_partial U x).mpr ⟨n, hp⟩)⟩
    · intro hx
      obtain ⟨n, hn⟩ := (mem_sequenceUnion U x).mp hx
      refine ⟨hUY n hn, fun hall => ?_⟩
      exact (ZFSet.mem_sep.mp (hall (n + 1))).2
        ((mem_partialUnion U (n + 1) x).mpr ⟨n, Nat.lt_succ_self n, hn⟩)
  rw [← he]
  exact h.diff_mem Y hY _ hI

/-- Density can be expressed by actual positive subsets after intersecting representatives. -/
def DenseRepresentativeFamily (E Y : ZFSet.{u}) : Prop :=
  ∀ A ∈ D, A ⊆ Y → 0 < h.value A → ∃ B ∈ E, B ⊆ A ∧ 0 < h.value B

lemma conull_of_approximate_covers {E Y C : ZFSet.{u}} (hY : Y ∈ D) (hC : C ∈ D)
    (hdense : h.DenseRepresentativeFamily E Y) (U : ℕ → ZFSet.{u})
    (hUC : ∀ n, U n ⊆ C)
    (happrox : ∀ n, ∀ B ∈ E, h.value (B \ U n) ≤ 1 / (n + 1 : ℝ)) :
    h.value (Y \ C) = 0 := by
  apply le_antisymm _ (h.value_nonneg (h.diff_mem Y hY C hC))
  by_contra hn
  obtain ⟨B, hBE, hBA, hB⟩ := hdense (Y \ C) (h.diff_mem Y hY C hC)
    (fun _ hx => (ZFSet.mem_sdiff.mp hx).1) (lt_of_not_ge hn)
  have he (n : ℕ) : B \ U n = B := by
    ext x
    rw [ZFSet.mem_sdiff]
    exact ⟨And.left, fun hx => ⟨hx, fun hu => (ZFSet.mem_sdiff.mp (hBA hx)).2 (hUC n hu)⟩⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / h.value B)
  have hv := happrox n B hBE
  rw [he] at hv
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hsmall := (le_div_iff₀ hden).mp hv
  have hlarge := (div_lt_iff₀ hB).mp hn
  nlinarith

end FiniteAdditiveCutGraph

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internally chosen finite covers
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    For each $n$, apply the finite approximation lemma with $\varepsilon=1/(n+1)$.
    The graph of the resulting finite list belongs to $M$ by §{sec:internal-borel-inputs}, and its finite union
    belongs to $D$, hence to $M$. Thus its ordered pair with that union belongs to $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    To choose all these pairs internally, bound the candidate graph $f$ by
    $K:=\InternalPowerSet{M}{\omega\times E}$ and its union $U$ by $D$.
    Require $f:k\to E$ for some $k\in\omega$, require $U\IncludedIn Y$, and express the union by
    $$x\in U\quad\longleftrightarrow\quad
    \exists B\in E\;\exists i\in\omega\;(\langle i,B\rangle\in f\ \land\ x\in B)
    \qquad(x\in Y).$$
    For every $B\in E$, choose $W\in D$ and $V\in R$ with
    $$W=\SetDifference{B}{U},\qquad\langle W,V\rangle\in F,\qquad\langle1,n+1\rangle\notin V.$$
    The last condition is exactly $\nu(W)\le1/(n+1)$ because $V$ is the strict rational cut for $\nu(W)$.
    Successor identifies $n+1$ inside $\omega$, and the difference equation is a bounded membership test.
    All these conditions therefore form one bounded predicate on $n$ and the output pair.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Apply the shared reflection theorem and internal countable choice to this predicate. This produces the entire
    sequence of pairs in $M$. Bounded projection and graph collection give both component sequences in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    For the final assertion, first check $C\in D$ using only internal families.
    Put $P_n:=\bigcup_{i<n}U_i$ and $W_n:=\SetDifference{Y}{P_n}$.
    The partial-union and relative-complement constructions put both whole sequence graphs in $M$.
    The sets $W_n\in D$ decrease. Internal continuity from above gives $\bigcap_nW_n\in D$, and taking its
    complement in $Y$ gives $C\in D$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    If $\nu(\SetDifference{Y}{C})>0$, the density hypothesis supplies $B\in E$ with
    $B\IncludedIn\SetDifference{Y}{C}$ and $\nu(B)>0$. Since every $U_n$ lies in $C$,
    $$0<\nu(B)=\nu(\SetDifference{B}{U_n})\le\frac1{n+1}\qquad(n\in\omega),$$
    which is impossible. Nonnegativity proves that the complement has measure zero.
-/
theorem internal_conull_finite_covers {M D R F E Y : ZFSet.{u}}
    (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (h : FiniteAdditiveCutGraph D R F)
    (hca : h.CountablyAdditiveOn M) (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M)
    (hE : E ∈ M) (hYM : Y ∈ M) (hY : Y ∈ D)
    (hED : ∀ B ∈ E, B ∈ D) (hEY : ∀ B ∈ E, B ⊆ Y)
    (hdense : h.DenseRepresentativeFamily E Y) :
    ∃ f U : ℕ → ZFSet.{u}, sequenceGraph (fun n => pair (f n) (U n)) ∈ M ∧
      sequenceGraph f ∈ M ∧ sequenceGraph U ∈ M ∧
      (∀ n, (∃ k : ℕ, IsFunc (natOrdinal k) E (f n)) ∧ U n ∈ D ∧
        U n = sUnion (graphRange (f n)) ∧
        ∀ B ∈ E, h.value (B \ U n) ≤ 1 / (n + 1 : ℝ)) ∧
      sequenceUnion U ∈ D ∧ h.value (Y \ sequenceUnion U) = 0 := by
  obtain ⟨f, U, hpairs, hfG, hUG, hu⟩ := internal_finite_approximate_covers
    hM hinf hpair hunion hpower hsep hrep hchoice h hD hR hF hE hYM hY hED hEY
  have hUY (n : ℕ) : U n ⊆ Y := by
    intro x hx
    rw [(hu n).2.2.1] at hx
    obtain ⟨B, hB, hxB⟩ := ZFSet.mem_sUnion.mp hx
    obtain ⟨i, hi⟩ := mem_graphRange.mp hB
    obtain ⟨k, hk⟩ := (hu n).1
    exact hEY B (ZFSet.pair_mem_prod.mp (hk.1 hi)).2 hxB
  have hC := h.internal_union_domain hM hinf hpair hunion hsep hrep hca hYM hY U hUG
    (fun n => (hu n).2.1) hUY
  refine ⟨f, U, hpairs, hfG, hUG, hu, hC, ?_⟩
  exact h.conull_of_approximate_covers hY hC hdense U
    (fun n _ hx => (mem_sequenceUnion U _).mpr ⟨n, hx⟩) (fun n => (hu n).2.2.2)

end PolishSpaceBook.CantorTreeMeasure
