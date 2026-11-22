module

public import PolishSpaceBook.SetTheoryInternalDependentChoice
public import PolishSpaceBook.SetTheoryInternalRelationRanks
public import PolishSpaceBook.SetTheoryTreeRanks
public import PolishSpaceBook.BorelPointGraphs

@[expose] public section

/-! # Internal branches and absolute well-foundedness of coded trees

An internal descending sequence of finite-word graphs has an internal union.
Its strictly growing domains make that union a branch on the actual natural
numbers. Internal dependent choice therefore turns failure of subset minima
into an internal branch.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BorelExpression
universe u

lemma mem_union_sequenceRange {s : ℕ → ZFSet.{u}} {p : ZFSet.{u}} :
    p ∈ ZFSet.sUnion (graphRange (sequenceGraph s)) ↔ ∃ n, p ∈ s n := by
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨a, ha⟩ := mem_graphRange.mp hy
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp ha
    have he := (ZFSet.pair_inj.mp hn).2
    exact ⟨n, he.symm ▸ hp⟩
  · rintro ⟨n, hp⟩
    exact ⟨s n, mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph s n _).mpr rfl⟩, hp⟩

/-- The union of an internal strict-extension chain is an internal branch. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal union of an extension chain
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The range and union constructions give $g\in M$, and membership in $g$ means membership in some $e(t_n)$.
    Induction gives $n\le |t_n|$. In particular,
    $$k<k+1\le |t_{k+1}|,\qquad
    \langle k,t_{k+1}(k)\rangle\in e(t_{k+1})\IncludedIn g.$$
    Thus every natural-number coordinate occurs in $g$. If two values for the same coordinate occur in $e(t_i)$
    and $e(t_j)$, both pairs belong to $e(t_{\max(i,j)})$ and the values are equal. Thus $g$ is a function graph on
    $\omega$ with values in $\omega$.
    Write it as $g_p$ using the point-graph correspondence of §{sec:internal-borel-sets}.
    For each $n$, the first $n$ values of $p$ agree with those of $t_n$:
    $$\restrict{p}{n}=\restrict{t_n}{n}.$$
    This prefix belongs to $T$ because $t_n\in T$ and $T$ is downward closed. Therefore $p\in\TreeBody{T}$.
-/
theorem internal_union_extension_chain {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List ℕ)) (hT : IsSubtree T) (s : ℕ → ZFSet.{u})
    (hs : ∀ n, s n ∈ wordTreeSet T)
    (hstep : ∀ n, pair (s (n + 1)) (s n) ∈ wordExtensionRelation (wordTreeSet T))
    (hg : sequenceGraph s ∈ M) :
    ∃ p : ℕ → ℕ, p ∈ treeBody T ∧
      pointGraph p = ZFSet.sUnion (graphRange (sequenceGraph s)) ∧ pointGraph p ∈ M := by
  have hwords (n : ℕ) : ∃ t ∈ T, wordGraph t = s n := mem_wordTreeSet.mp (hs n)
  choose t ht hts using hwords
  have hprefix (n : ℕ) : (t n).IsPrefix (t (n + 1)) ∧ (t n).length < (t (n + 1)).length := by
    have h := hstep n
    rw [← hts n, ← hts (n + 1)] at h
    exact (wordExtensionRelation_iff ⟨t (n + 1), ht _⟩ ⟨t n, ht _⟩).mp h
  have hlen (n : ℕ) : n ≤ (t n).length := by
    induction n with
    | zero => omega
    | succ n ih => have h := (hprefix n).2; omega
  have hmono {n m : ℕ} (hnm : n ≤ m) : s n ⊆ s m := by
    induction hnm with
    | refl => exact fun _ h => h
    | @step m _ ih =>
      exact fun _ h => (pair_mem_wordExtensionRelation.mp (hstep m)).2.2.1 (ih h)
  let U := ZFSet.sUnion (graphRange (sequenceGraph s))
  have hUM : U ∈ M := union_mem hM hunion (graphRange_mem hM hunion (hsep _) hg)
  have hsU (n : ℕ) : s n ⊆ U := fun _ hp => mem_union_sequenceRange.mpr ⟨n, hp⟩
  have hfunc : IsFunc Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet U := by
    constructor
    · intro p hp
      obtain ⟨n, hn⟩ := mem_union_sequenceRange.mp hp
      rw [← hts n] at hn
      obtain ⟨i, rfl⟩ := mem_wordGraph.mp hn
      exact ZFSet.pair_mem_prod.mpr
        ⟨mem_omegaOrdinal.mpr ⟨i.val, rfl⟩, mem_omegaOrdinal.mpr ⟨(t n).get i, rfl⟩⟩
    · intro a ha
      obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp ha
      have hk : k < (t (k + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self k) (hlen (k + 1))
      have hkpair : pair (natOrdinal k) (natOrdinal (t (k + 1))[k]) ∈ s (k + 1) := by
        rw [← hts (k + 1)]
        exact pair_mem_wordGraph.mpr ⟨hk, rfl⟩
      refine ⟨natOrdinal (t (k + 1))[k], hsU _ hkpair, ?_⟩
      intro y hy
      obtain ⟨n, hn⟩ := mem_union_sequenceRange.mp hy
      let m := max n (k + 1)
      have hny : pair (natOrdinal k) y ∈ wordGraph (t m) :=
        (hts m).symm ▸ hmono (Nat.le_max_left n (k + 1)) hn
      have hky : pair (natOrdinal k) (natOrdinal (t (k + 1))[k]) ∈ wordGraph (t m) :=
        (hts m).symm ▸ hmono (Nat.le_max_right n (k + 1)) hkpair
      have hdom := (ZFSet.pair_mem_prod.mp ((wordGraph_isFunc (t m)).1 hny)).1
      exact ((wordGraph_isFunc (t m)).2 _ hdom).unique hny hky
  obtain ⟨p, hp⟩ := exists_pointGraph_of_isFunc hfunc
  refine ⟨p, ?_, hp, hp.symm ▸ hUM⟩
  intro n
  have hsub : wordGraph (t n) ⊆ pointGraph p := by
    rw [hp, hts n]
    exact hsU n
  have hcyl := (wordGraph_subset_pointGraph (t n) p).mp hsub
  have he : seqPrefix p n = (t n).take n := by
    apply List.ext_getElem
    · simp [seqPrefix_length, List.length_take, Nat.min_eq_left (hlen n)]
    · intro i hi hi'
      have hin : i < n := by simpa only [seqPrefix_length] using hi
      have hval := hcyl i (lt_of_lt_of_le hin (hlen n))
      simpa [seqPrefix] using hval
  rw [he]
  exact hT (ht n) (List.take_prefix n _)

/-- The branch-existence consequence of the explicit union identity. -/
theorem internal_branch_of_extension_chain {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List ℕ)) (hT : IsSubtree T) (s : ℕ → ZFSet.{u})
    (hs : ∀ n, s n ∈ wordTreeSet T)
    (hstep : ∀ n, pair (s (n + 1)) (s n) ∈ wordExtensionRelation (wordTreeSet T))
    (hg : sequenceGraph s ∈ M) :
    ∃ p : ℕ → ℕ, p ∈ treeBody T ∧ pointGraph p ∈ M := by
  obtain ⟨p, hp, _, hg⟩ := internal_union_extension_chain hM hunion hsep T hT s hs hstep hg
  exact ⟨p, hp, hg⟩

/-- Failure of internal subset minima yields a branch whose whole graph is internal. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal absence of branches implies well-foundedness
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Otherwise, some nonempty $B\in M$ with $B\IncludedIn W$ has no $R$-minimal element. Every $x\in B$ then has
    $y\in B$ with $\langle y,x\rangle\in R$. Choose $a\in B$ and apply internal dependent choice. It gives an internal
    graph $G_s$ of a sequence in $B$ satisfying $\langle s(n+1),s(n)\rangle\in R$. Each $s(n)$ is the finite graph
    $e(t_n)$ of a unique node $t_n\in T$. The definition of $R_W$ says that $t_{n+1}$ strictly extends $t_n$.
    The union lemma therefore produces a branch whose graph belongs to $M$, a contradiction.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Absence of internal branches supplies both the subset-minimum assertion
    and the rank.
-/
theorem internal_tree_minima_of_no_internal_branch {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hchoice : M ⊨ choiceSentence) (T : Set (List ℕ)) (hT : IsSubtree T) (W R : M)
    (hW : W.val = wordTreeSet T) (hR : R.val = wordExtensionRelation W.val)
    (hno : ¬ ∃ p : ℕ → ℕ, p ∈ treeBody T ∧ pointGraph p ∈ M) :
    internalOrderMinimaFormula.Realize Empty.elim ![W, R] := by
  apply (realize_internalOrderMinimaFormula hM W R).mpr
  intro B hBW hne
  by_contra hbad
  have hserial : ∀ x ∈ B.val, ∃ y ∈ B.val, pair y x ∈ R.val := by
    intro x hx
    by_contra hn
    apply hbad
    exact ⟨x, hx, fun y hy hyx => hn ⟨y, hy, hyx⟩⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨s, _, hs, hstep, hg⟩ := internal_dependent_choice hM hinf hpair hunion hpower hsep
    hchoice B R hserial ⟨a, ha⟩
  apply hno
  apply internal_branch_of_extension_chain hM hunion hsep T hT s
  · intro n
    exact hW ▸ hBW (hs n)
  · intro n
    simpa only [hR, hW] using hstep n
  · exact hg

/-- The internal subset-minimum construction supplies an actual internal rank
for a tree without an internal branch. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Absence of internal branches supplies both the subset-minimum assertion
    and the rank.
-/
theorem internal_tree_rank_of_no_internal_branch {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (T : Set (List ℕ)) (hT : IsSubtree T) (W R : M)
    (hW : W.val = wordTreeSet T) (hR : R.val = wordExtensionRelation W.val)
    (hno : ¬ ∃ p : ℕ → ℕ, p ∈ treeBody T ∧ pointGraph p ∈ M) :
    ∃ α f : M, rankCertificateFormula.Realize Empty.elim ![W, R, α, f] := by
  have hmin := internal_tree_minima_of_no_internal_branch hM hinf hpair hunion hpower hsep
    hchoice T hT W R hW hR hno
  exact internal_rank_certificate hM hinf hpair hunion hpower hsep hrep hchoice W R hmin

/-- New external branches cannot appear in a tree that has no internal branch. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal absence of branches implies well-foundedness
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Thus $M\models\chi(W,R)$. §{sec:internal-rank-existence} now constructs an internal rank, and
    §{sec:internal-rank-certificates} excludes every external branch.
-/
theorem no_external_branch_of_no_internal_branch {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (T : Set (List ℕ)) (hT : IsSubtree T) (W R : M)
    (hW : W.val = wordTreeSet T) (hR : R.val = wordExtensionRelation W.val)
    (hno : ¬ ∃ p : ℕ → ℕ, p ∈ treeBody T ∧ pointGraph p ∈ M) :
    ¬ ∃ p, p ∈ treeBody T := by
  obtain ⟨α, f, hr⟩ := internal_tree_rank_of_no_internal_branch hM hinf hpair hunion hpower
    hsep hrep hchoice T hT W R hW hR hno
  exact no_branch_of_internal_tree_rank hM T hT W R α f hW hR hr

end PolishSpaceBook.SetTheoryModels
