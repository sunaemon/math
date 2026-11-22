module

public import PolishSpaceBook.SetTheoryRankCertificates
public import PolishSpaceBook.SetTheoryInternalFiniteSequences
public import PolishSpaceBook.SetTheoryInternalOrderMinima
public import PolishSpaceBook.TreeWellFounded

@[expose] public section

/-! # Set-coded tree relations and internal ranks that exclude external branches -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Code each node by its finite function graph. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    We next connect this formula to the word trees used above. Code a finite word $s$ by its finite function graph
    $e(s)$ from §{sec:internal-borel-inputs}, and for a tree $Q$ put
    $$W_Q:=\{e(s):s\in Q\}.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Encode binary words as finite graphs with values in $2=\{0,1\}$, and write
    $$W_O:=\{e(s):s\in O\},\qquad U(O):=\bigcup_{s\in O}\cyl{s}$$
    for a family $O\IncludedIn\finseq{2}$. An internal open code means that $W_O\in M$.
-/
def wordTreeSet (T : Set (List ℕ)) : ZFSet.{u} :=
  ZFSet.range (fun s : T => wordGraph s.val)

lemma mem_wordTreeSet {T : Set (List ℕ)} {x : ZFSet.{u}} :
    x ∈ wordTreeSet T ↔ ∃ s ∈ T, wordGraph s = x := by
  simp only [wordTreeSet, ZFSet.mem_range, Subtype.exists, exists_prop]

lemma wordGraph_mem_wordTreeSet {T : Set (List ℕ)} {s : List ℕ} :
    wordGraph s ∈ wordTreeSet.{u} T ↔ s ∈ T := by
  rw [mem_wordTreeSet]
  exact ⟨fun ⟨t, ht, he⟩ => wordGraph_injective he ▸ ht, fun hs => ⟨s, hs, rfl⟩⟩

/-- Parameters W,p; p codes a strictly extending word followed by its prefix. -/
def wordExtensionPredicate : BoundedSetPredicate 2 :=
  .ex 0 (.ex 0 (.conj (.conj (.orderedPair (1 : Fin 4) 2 3) (.subset 3 2))
    (.neg (.equal 3 2))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Separate its elements using
    $$\begin{aligned}
    \eta(W,p)\;:\equiv\;\exists a,b\in W\,\bigl(&p=\langle a,b\rangle\\
    &{}\land\bigl(\forall z\in b\;(z\in a)\bigr)\land b\ne a\bigr).
    \end{aligned}$$
-/
def wordExtensionFormula : ForcingFormulas.Formula 2 := wordExtensionPredicate.compile

lemma wordExtensionFormula_deltaZero : IsDeltaZero wordExtensionFormula :=
  wordExtensionPredicate.compile_deltaZero

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For an arbitrary set $W$, define the descending relation
    $$R_W:=\{\langle a,b\rangle\in W\times W:b\IncludedIn a\land b\ne a\}.$$
    On $W_Q$ this is precisely strict word extension, with the longer word first.
-/
def wordExtensionRelation (W : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod W W).sep (fun p => ∃ x ∈ W, ∃ y ∈ W, p = pair x y ∧ y ⊆ x ∧ y ≠ x)

lemma pair_mem_wordExtensionRelation {W x y : ZFSet.{u}} :
    pair x y ∈ wordExtensionRelation W ↔ x ∈ W ∧ y ∈ W ∧ y ⊆ x ∧ y ≠ x := by
  rw [wordExtensionRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, _, b, _, he, hsub, hne⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx, hy, hsub, hne⟩
  · rintro ⟨hx, hy, hsub, hne⟩
    exact ⟨⟨hx, hy⟩, x, hx, y, hy, rfl, hsub, hne⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The ordered-pair equality has a bounded expansion, so $\eta$ is $\Delta_0$. Transitivity makes this predicate
    recognize exactly the displayed relation, and Separation puts that relation in $M$. This construction does not
    require a rank or an enumeration of branches.
-/
lemma realize_wordExtensionFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (W p : M) :
    wordExtensionFormula.Realize Empty.elim ![W, p] ↔
      ∃ x ∈ W.val, ∃ y ∈ W.val, p.val = pair x y ∧ y ⊆ x ∧ y ≠ x := by
  rw [wordExtensionFormula, BoundedSetPredicate.realize_compile hM]
  simp [wordExtensionPredicate, BoundedSetPredicate.eval, Fin.snoc, and_assoc]

/-- The extension relation needs no internal rank or branch enumeration to be constructed. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal strict-extension relation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The ordered-pair equality has a bounded expansion, so $\eta$ is $\Delta_0$. Transitivity makes this predicate
    recognize exactly the displayed relation, and Separation puts that relation in $M$. This construction does not
    require a rank or an enumeration of branches.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The product $W\times W$ belongs to $M$.
-/
theorem wordExtensionRelation_mem {M W : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hW : W ∈ M) : wordExtensionRelation W ∈ M := by
  apply separation_mem_of_absolute hM wordExtensionFormula (hsep _) ![⟨W, hW⟩]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) hW hW)
  intro p _
  have hs : Fin.snoc ![⟨W, hW⟩] p = ![⟨W, hW⟩, p] := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  exact realize_wordExtensionFormula hM ⟨W, hW⟩ p

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Graph inclusion and injectivity of $e$ give
    $$e(t)\IncludedIn e(s)\land e(t)\ne e(s)
    \quad\Longleftrightarrow\quad t\properPrefixOf s.$$
-/
lemma wordExtensionRelation_iff {T : Set (List ℕ)} (s t : T) :
    pair (wordGraph s.val) (wordGraph t.val) ∈ wordExtensionRelation (wordTreeSet.{u} T) ↔
      strictTreeExtension T s t := by
  rw [pair_mem_wordExtensionRelation, wordGraph_mem_wordTreeSet, wordGraph_mem_wordTreeSet,
    wordGraph_subset_iff]
  have hne : wordGraph.{u} t.val ≠ wordGraph s.val ↔ t.val ≠ s.val :=
    not_congr wordGraph_injective.eq_iff
  rw [hne]
  simp only [s.property, t.property, true_and]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨hp, lt_of_le_of_ne hp.length_le (fun he => hn (hp.eq_of_length_le he.ge))⟩
  · rintro ⟨hp, hl⟩
    exact ⟨hp, fun he => (Nat.lt_irrefl _) (he ▸ hl)⟩

/-- Extending a word lowers the ordinal value read from the rank graph. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For a rank certificate on $W_Q$ with relation $R_{W_Q}$, the comparison therefore reads
    $$t\properPrefixOf s\quad\Longrightarrow\quad f(e(s))\in f(e(t))
    \qquad(t,s\in Q).$$
-/
lemma rankCertificate_word_values {T : Set (List ℕ)} {α f a b : ZFSet.{u}}
    (hr : IsRankCertificate (wordTreeSet T) (wordExtensionRelation (wordTreeSet T)) α f)
    (s t : T) (hst : strictTreeExtension T s t)
    (ha : pair (wordGraph s.val) a ∈ f) (hb : pair (wordGraph t.val) b ∈ f) : a ∈ b := by
  exact hr.2.2 (wordGraph s.val) (wordGraph_mem_wordTreeSet.mpr s.property)
    (wordGraph t.val) (wordGraph_mem_wordTreeSet.mpr t.property)
    a (ZFSet.pair_mem_prod.mp (hr.2.1.1 ha)).2
    b (ZFSet.pair_mem_prod.mp (hr.2.1.1 hb)).2
    ((wordExtensionRelation_iff s t).mpr hst) ha hb

/-- Pull a set-coded rank back to the original words. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The certificate gives actual well-foundedness on $W_Q$. Pull this relation back along $e:Q\to W_Q$.
    The graph-inclusion equivalence identifies the pullback with strict word extension. Thus that extension relation
    is well-founded.
-/
theorem tree_wellFounded_of_rankCertificate {T : Set (List ℕ)} {α f : ZFSet.{u}}
    (hr : IsRankCertificate (wordTreeSet T) (wordExtensionRelation (wordTreeSet T)) α f) :
    WellFounded (strictTreeExtension T) := by
  let j : T → wordTreeSet.{u} T := fun s => ⟨wordGraph s.val, wordGraph_mem_wordTreeSet.mpr s.property⟩
  apply (InvImage.wf j hr.wellFounded).mono
  intro s t hst
  exact (wordExtensionRelation_iff s t).mpr hst

/-- An internally recognized certificate excludes every external branch of the coded tree. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal tree ranks exclude external branches
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The successive prefixes of any branch would give a descending sequence, a contradiction.
-/
theorem no_branch_of_internal_tree_rank {M : ZFSet.{u}} (hM : M.IsTransitive)
    (T : Set (List ℕ)) (hT : IsSubtree T) (W R α f : M)
    (hW : W.val = wordTreeSet T) (hR : R.val = wordExtensionRelation W.val)
    (hr : rankCertificateFormula.Realize Empty.elim ![W, R, α, f]) :
    ¬ ∃ z, z ∈ treeBody T := by
  have hcert := (realize_rankCertificateFormula hM W R α f).mp hr
  rw [hR, hW] at hcert
  exact (prefixTreeWellFounded_iff T hT).mpr (tree_wellFounded_of_rankCertificate hcert)

end PolishSpaceBook.SetTheoryModels
