module

public import PolishSpaceBook.FiniteMeasureCoverPredicates

@[expose] public section

/-! # Internally chosen sequences of finite approximate covers -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas
open FiniteMeasureCover FiniteAdditiveCutGraph
universe u

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
theorem internal_finite_approximate_covers {M D R F E Y : ZFSet.{u}}
    (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (h : FiniteAdditiveCutGraph D R F)
    (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) (hE : E ∈ M) (hYM : Y ∈ M) (hY : Y ∈ D)
    (hED : ∀ B ∈ E, B ∈ D) (hEY : ∀ B ∈ E, B ⊆ Y) :
    ∃ f U : ℕ → ZFSet.{u}, sequenceGraph (fun n => pair (f n) (U n)) ∈ M ∧
      sequenceGraph f ∈ M ∧ sequenceGraph U ∈ M ∧
      ∀ n, (∃ k : ℕ, IsFunc (natOrdinal k) E (f n)) ∧ U n ∈ D ∧
        U n = sUnion (graphRange (f n)) ∧
        ∀ B ∈ E, h.value (B \ U n) ≤ 1 / (n + 1 : ℝ) := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let K : M := ⟨internalPowerSet M (ZFSet.prod Ω.val E),
    internalPowerSet_mem hM hpower
      (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property hE)⟩
  let one : M := ⟨natOrdinal 1, hM.mem_trans (mem_omegaOrdinal.mpr ⟨1, rfl⟩) Ω.property⟩
  let ps : Fin 8 → M := ![Ω, ⟨E, hE⟩, ⟨Y, hYM⟩, ⟨D, hD⟩, ⟨R, hR⟩, ⟨F, hF⟩, K, one]
  have heval (n : ℕ) (y : M) :
      coverPredicate.eval (Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val) ↔
        ∃ f ∈ K.val, ∃ U ∈ D, y.val = pair f U ∧ (∃ k : ℕ, IsFunc (natOrdinal k) E f) ∧
          U = sUnion (graphRange f) ∧ ∀ B ∈ E, h.value (B \ U) ≤ 1 / (n + 1 : ℝ) := by
    have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val =
        ![Ordinal.omega0.toZFSet, E, Y, D, R, F, K.val, natOrdinal 1, natOrdinal n, y.val] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact eval_coverPredicate h hED hEY n y.val
  obtain ⟨s, hs, hp⟩ := bounded_countable_choice hM hinf hpair hunion hpower hsep hrep hchoice
    coverPredicate ps (by
      intro n
      obtain ⟨l, hl, hv⟩ := h.exists_finite_approximate_cover hY hED hEY
        (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity)
      have hf := listGraph_isFunc l hl
      have hfM := finite_function_mem hM hinf hpair hunion hE hf
      have hfK : listGraph l ∈ K.val := by
        change listGraph l ∈ M.sep (fun f => f ⊆ ZFSet.prod Ω.val E)
        apply ZFSet.mem_sep.mpr
        refine ⟨hfM, ?_⟩
        intro p hpf
        obtain ⟨i, hi, B, hB, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hpf)
        obtain ⟨j, _, rfl⟩ := mem_natOrdinal.mp hi
        exact ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨j, rfl⟩, hB⟩
      have hU := h.listUnion_mem l (fun B hB => hED B (hl B hB))
      let y : M := ⟨pair (listGraph l) (listUnion l),
        orderedPair_mem hM hpair hfM (hM.mem_trans hU hD)⟩
      refine ⟨y, (heval n y).mpr ?_⟩
      exact ⟨listGraph l, hfK, listUnion l, hU, rfl, ⟨l.length, hf⟩, (listGraph_union l).symm, hv⟩)
  have hw (n : ℕ) := (heval n (s n)).mp (hp n)
  choose f hf U hU he hk hu hv using hw
  have hfM (n : ℕ) : f n ∈ M := hM.mem_trans (hf n) K.property
  have hUM (n : ℕ) : U n ∈ M := hM.mem_trans (hU n) hD
  have hpairs : sequenceGraph (fun n => pair (f n) (U n)) ∈ M := by
    have heq : (fun n => (s n).val) = (fun n => pair (f n) (U n)) := funext he
    rwa [heq] at hs
  have hfg := pairSequence_projection_mem hM hinf hpair hunion hsep hrep
    (fun n => ⟨f n, hfM n⟩) (fun n => ⟨U n, hUM n⟩) hpairs true
  have hUg := pairSequence_projection_mem hM hinf hpair hunion hsep hrep
    (fun n => ⟨f n, hfM n⟩) (fun n => ⟨U n, hUM n⟩) hpairs false
  exact ⟨f, U, hpairs, hfg, hUg, fun n => ⟨hk n, hU n, hu n, hv n⟩⟩

end PolishSpaceBook.CantorTreeMeasure
