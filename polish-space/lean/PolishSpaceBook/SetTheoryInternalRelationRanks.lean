module

public import PolishSpaceBook.SetTheoryMinimumSelection
public import PolishSpaceBook.SetTheoryChoiceEnumeration
public import PolishSpaceBook.SetTheoryRankCertificates

@[expose] public section

/-! # Internal ordinal-valued ranks for internally well-founded relations

Remove a relation-minimal element at each stage. The internal Hartogs bound
forces exhaustion. The inverse enumeration is an internal rank certificate;
no external well-foundedness or linearity of the relation is assumed.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal enumeration respecting a relation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Use the selector $c$ from the lemma and the internal Hartogs bound $H$ for $W$ from §{sec:internal-hartogs-bound}.
    Run the internal selection recursion of §{sec:internal-choice-recursion} on $H$. At stage $\beta$, its remaining set is
    $$r_\beta:=\SetDifference{W}{\GraphRange{\restrict{f}{\beta}}}.$$
    The recurrence selects $c(r_\beta)$ if this set is nonempty and the empty set otherwise. Its graph $f$ belongs to
    $M$. If every remainder were nonempty, the selected values would be distinct members of $W$, giving an internal
    injection from $H$ into $W$, contrary to the Hartogs bound. Let $\gamma\in H$ be the first stage with empty remainder.
    Then $\gamma\in M$ by transitivity and $e:=\restrict{f}{\gamma}\in M$ by graph restriction. As in
    §{sec:internal-choice-enumerations}, every earlier remainder is nonempty, so $e$ is injective; the empty remainder
    at $\gamma$ makes it onto $W$. This includes $W=\emptyset$, when $\gamma=0$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    It remains to check the relation. Suppose $x=e(\alpha)$, $y=e(\beta)$, and $\langle x,y\rangle\in R$.
    The value $y=c(r_\beta)$ is $R$-minimal in $r_\beta$. Thus $x\notin r_\beta$ and $x$ already appears in the graph
    $\restrict{f}{\beta}$. Let $\delta\in\beta$ be an index with $f(\delta)=x$. Since $\beta\in\gamma$, also
    $\delta\in\gamma$, and injectivity of $e$ gives $\delta=\alpha$. Hence $\alpha\in\beta$, as required.
-/
theorem internal_minimum_enumeration {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W R : M)
    (hmin : internalOrderMinimaFormula.Realize Empty.elim ![W, R]) :
    ∃ γ e : M, γ.val.IsOrdinal ∧ IsFunc γ.val W.val e.val ∧
      (∀ x ∈ W.val, ∃ a ∈ γ.val, pair a x ∈ e.val) ∧
      (∀ a b x, pair a x ∈ e.val → pair b x ∈ e.val → a = b) ∧
      (∀ a b x y, pair a x ∈ e.val → pair b y ∈ e.val → pair x y ∈ R.val → a ∈ b) := by
  obtain ⟨c, hc, hs, hminimal⟩ := internal_minimum_selector hM hpair hunion hpower hsep hchoice W R hmin
  obtain ⟨H, hH, hbound⟩ := internal_hartogs_bound hM hpair hunion hpower hsep (hrep _) W
  obtain ⟨f, hf, _⟩ := internal_fresh_recursion hM (empty_mem_of_infinity hM hinf)
    hpair hunion hpower hsep hrep W c H hH.isTransitive hc hs
  have hex := selection_exhausts hM hunion hsep W c H f hH hc hs hf hbound
  let S : Set ZFSet.{u} := {a | a ∈ H.val ∧ ¬ ∃ z, z ∈ remainingSet W.val (restrictGraph f.val a)}
  obtain ⟨γ, hγ, hfirst⟩ := ZFSet.mem_wf.has_min S hex
  have hγH : γ ∈ H.val := hγ.1
  have hγM := hM.mem_trans hγH H.property
  have hγord := hH.mem hγH
  have hγsub : γ ⊆ H.val := hH.subset_of_mem hγH
  have hne (a : ZFSet.{u}) (ha : a ∈ γ) : ∃ z, z ∈ remainingSet W.val (restrictGraph f.val a) := by
    by_contra hnot
    exact hfirst a ⟨hγsub ha, hnot⟩ ha
  have hnew : ∀ a ∈ γ, ∀ b, pair a b ∈ f.val →
      b ∈ W.val ∧ b ∉ graphRange (restrictGraph f.val a) := by
    intro a ha b hb
    exact selection_value_fresh hM hunion hsep W c H f hc hs hf (hγsub ha) hb (hne a ha)
  have horder (a b x y : ZFSet.{u}) (ha : a ∈ γ) (hb : b ∈ γ)
      (hax : pair a x ∈ f.val) (hby : pair b y ∈ f.val) (hxy : pair x y ∈ R.val) : a ∈ b := by
    let U := remainingSet W.val (restrictGraph f.val b)
    have hU : U ∈ M := remainingSet_mem hM hunion (hsep _) W.property
      (restrictGraph_mem hM hunion (hsep _) f.property (hM.mem_trans hb hγM))
    have hUW : U ⊆ W.val := fun _ hz => (mem_remainingSet.mp hz).1
    have hUS : U ∈ internalNonemptySubsets M W.val :=
      mem_internalNonemptySubsets.mpr ⟨⟨hU, hUW⟩, hne b hb⟩
    have hy : y = freshValue U c.val := (hf.function_graph.2 b (hγsub hb)).unique
      hby (hf.equation b (hγsub hb))
    have hyc : pair U y ∈ c.val := by
      rcases (freshValue_spec hc hs hU hUW y).mp hy with h | h
      · exact h.2
      · exact False.elim (h.1 (hne b hb))
    have hxrange : x ∈ graphRange (restrictGraph f.val b) := by
      by_contra hn
      exact hminimal U hUS y hyc x (mem_remainingSet.mpr ⟨(hnew a ha x hax).1, hn⟩) hxy
    obtain ⟨d, hd⟩ := mem_graphRange.mp hxrange
    obtain ⟨hdx, hdb⟩ := pair_mem_restrictGraph.mp hd
    have hdγ : d ∈ γ := hγord.isTransitive.mem_trans hdb hb
    have hda : d = a := selection_injective_on hH hγsub
      (fun t ht z hz => (hnew t ht z hz).2) hdγ ha hdx hax
    exact hda ▸ hdb
  let e : M := ⟨restrictGraph f.val γ, restrictGraph_mem hM hunion (hsep _) f.property hγM⟩
  have he : IsFunc γ W.val e.val := by
    refine ⟨?_, (isFunc_restrictGraph hf.function_graph hγsub).2⟩
    intro p hp
    obtain ⟨a, ha, b, rfl, hab⟩ := mem_restrictGraph.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨ha, (hnew a ha b hab).1⟩
  refine ⟨⟨γ, hγM⟩, e, hγord, he, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hnot
    apply hγ.2
    refine ⟨x, mem_remainingSet.mpr ⟨hx, ?_⟩⟩
    intro hxrange
    obtain ⟨a, ha⟩ := mem_graphRange.mp hxrange
    exact hnot ⟨a, (pair_mem_restrictGraph.mp ha).2, ha⟩
  · intro a b x hax hbx
    obtain ⟨hax', ha⟩ := pair_mem_restrictGraph.mp hax
    obtain ⟨hbx', hb⟩ := pair_mem_restrictGraph.mp hbx
    exact selection_injective_on hH hγsub (fun a ha b hb => (hnew a ha b hb).2) ha hb hax' hbx'
  · intro a b x y hax hby hxy
    obtain ⟨hax', ha⟩ := pair_mem_restrictGraph.mp hax
    obtain ⟨hby', hb⟩ := pair_mem_restrictGraph.mp hby
    exact horder a b x y ha hb hax' hby' hxy

/-- Internal subset minima and the model axioms produce an actual internal rank graph. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Internal existence of a rank certificate
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Take the ordinal enumeration $e:\gamma\to W$ from the theorem. Its inverse graph $g:W\to\gamma$ belongs to $M$:
    separate from $W\times\gamma$ the reversed pairs of $e$. For $x,y\in W$, the enumeration property gives
    $$\langle x,y\rangle\in R\quad\Longrightarrow\quad g(x)\in g(y).$$
    Thus $g$ is a rank with ordinal bound $\gamma$. The recognition lemma of §{sec:internal-rank-certificates} gives
    the asserted internal formula.
-/
theorem internal_rank_certificate {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W R : M)
    (hmin : internalOrderMinimaFormula.Realize Empty.elim ![W, R]) :
    ∃ α f : M, rankCertificateFormula.Realize Empty.elim ![W, R, α, f] := by
  obtain ⟨γ, e, hγ, he, honto, hinj, horder⟩ :=
    internal_minimum_enumeration hM hinf hpair hunion hpower hsep hrep hchoice W R hmin
  have hrange : graphRange e.val = W.val := by
    apply ZFSet.ext
    intro x
    constructor
    · rintro hx
      obtain ⟨a, ha⟩ := mem_graphRange.mp hx
      exact (ZFSet.pair_mem_prod.mp (he.1 ha)).2
    · intro hx
      obtain ⟨a, _, ha⟩ := honto x hx
      exact mem_graphRange.mpr ⟨a, ha⟩
  let f : M := ⟨inverseGraph e.val γ.val W.val,
    inverseGraph_mem hM hpair hunion hpower hsep e.property γ.property W.property⟩
  refine ⟨γ, f, (realize_rankCertificateFormula hM W R γ f).mpr ⟨hγ, ?_, ?_⟩⟩
  · have hf := inverseGraph_isFunc_of_injective he hinj
    simpa only [hrange] using hf
  · intro x _ y _ a _ b _ hxy hxa hyb
    exact horder a b x y (pair_mem_inverseGraph.mp hxa).2.2 (pair_mem_inverseGraph.mp hyb).2.2 hxy

/-- Internal well-foundedness is enough; external well-foundedness is a conclusion. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    In the forward direction, construct the internal rank graph and apply the preceding transfer theorem.
-/
theorem wellFounded_of_internal_minima {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W R : M)
    (hmin : internalOrderMinimaFormula.Realize Empty.elim ![W, R]) :
    WellFounded (fun x y : W.val => pair x.val y.val ∈ R.val) := by
  obtain ⟨α, f, hf⟩ := internal_rank_certificate hM hinf hpair hunion hpower hsep hrep hchoice W R hmin
  exact wellFounded_of_internal_rank hM W R α f hf

/-- Actual well-foundedness supplies minima for every internal nonempty subset. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, actual well-foundedness gives a minimal element in every nonempty subset of $W$, hence in each such
    subset belonging to $M$. Transitivity puts that element in $M$, and the interpretation of $\chi$ gives the result.
-/
theorem internal_minima_of_wellFounded {M : ZFSet.{u}} (hM : M.IsTransitive) (W R : M)
    (hw : WellFounded (fun x y : W.val => pair x.val y.val ∈ R.val)) :
    internalOrderMinimaFormula.Realize Empty.elim ![W, R] := by
  apply (realize_internalOrderMinimaFormula hM W R).mpr
  intro B hBW hne
  let S : Set W.val := {x | x.val ∈ B.val}
  have hS : S.Nonempty := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨⟨b, hBW hb⟩, hb⟩
  obtain ⟨a, ha, hamin⟩ := hw.has_min S hS
  exact ⟨a.val, ha, fun b hb hba => hamin ⟨b, hBW hb⟩ hb hba⟩

/-- The internal subset-minimum formula characterizes actual well-foundedness. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Internal and actual well-foundedness
-/
theorem internal_minima_iff_wellFounded {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W R : M) :
    internalOrderMinimaFormula.Realize Empty.elim ![W, R] ↔
      WellFounded (fun x y : W.val => pair x.val y.val ∈ R.val) :=
  ⟨wellFounded_of_internal_minima hM hinf hpair hunion hpower hsep hrep hchoice W R,
    internal_minima_of_wellFounded hM W R⟩

end PolishSpaceBook.SetTheoryModels
