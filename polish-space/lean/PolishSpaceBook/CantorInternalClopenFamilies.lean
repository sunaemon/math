module

public import PolishSpaceBook.CantorInternalLevelFamilies
public import PolishSpaceBook.BorelCantorGraphs

@[expose] public section

/-! # The internal decreasing clopen sequence of a binary tree -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

/-- The union of the cylinders named by a set of finite-word graphs. -/
def internalCylinderUnion (M W : ZFSet.{u}) : ZFSet.{u} :=
  (internalCantor M).sep (fun g => ∃ w ∈ W, w ⊆ g)

/-- Parameters word family, ambient points, and proposed cylinder union. -/
def cylinderUnionPredicate : BoundedSetPredicate 3 :=
  .conj (.subset 2 1) (.all 1 (.iff (.member 3 2) (.ex 0 (.subset 4 3))))

lemma eval_cylinderUnionPredicate (M W D : ZFSet.{u}) :
    cylinderUnionPredicate.eval ![W, internalCantor M, D] ↔ D = internalCylinderUnion M W := by
  change (D ⊆ internalCantor M ∧ ∀ g ∈ internalCantor M,
    g ∈ D ↔ ∃ w ∈ W, w ⊆ g) ↔ _
  constructor
  · rintro ⟨hs, he⟩
    ext g
    exact ⟨fun hg => ZFSet.mem_sep.mpr ⟨hs hg, (he g (hs hg)).mp hg⟩,
      fun hg => (he g (ZFSet.mem_sep.mp hg).1).mpr (ZFSet.mem_sep.mp hg).2⟩
  · rintro rfl
    exact ⟨fun _ hg => (ZFSet.mem_sep.mp hg).1, fun g hg => by
      simp only [internalCylinderUnion, ZFSet.mem_sep, hg, true_and]⟩

lemma internalCylinderUnion_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hY : internalCantor M ∈ M) (W : ZFSet.{u}) (hW : W ∈ M) :
    internalCylinderUnion M W ∈ M :=
  (BoundedSetPredicate.ex (0 : Fin 2) (.subset 2 1)).separation_mem hM (hsep _) ![⟨W, hW⟩] hY

/-- Parameters sequence graph, its range, ambient points, index, and output set. -/
def cylinderUnionSequencePredicate : BoundedSetPredicate 5 :=
  .ex 1 (.conj (.pairMember 0 3 5) (cylinderUnionPredicate.rename ![5, 2, 4]))

lemma eval_cylinderUnionSequencePredicate (M : ZFSet.{u}) (W : ℕ → ZFSet.{u}) (n : ℕ) (D : ZFSet.{u}) :
    cylinderUnionSequencePredicate.eval
      ![sequenceGraph W, graphRange (sequenceGraph W), internalCantor M, natOrdinal n, D] ↔
      D = internalCylinderUnion M (W n) := by
  simp only [cylinderUnionSequencePredicate, eval, eval_rename, Fin.snoc]
  change (∃ w ∈ graphRange (sequenceGraph W), pair (natOrdinal n) w ∈ sequenceGraph W ∧
    cylinderUnionPredicate.eval ![w, internalCantor M, D]) ↔ _
  simp only [pair_mem_sequenceGraph, eval_cylinderUnionPredicate]
  constructor
  · rintro ⟨w, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨W n, mem_graphRange.mpr ⟨natOrdinal n,
      (pair_mem_sequenceGraph W n _).mpr rfl⟩, rfl, h⟩

/-- Forming cylinder unions preserves internality of an entire sequence of word families. -/
theorem internalCylinderUnion_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hY : internalCantor M ∈ M) (W : ℕ → M) (hG : sequenceGraph (fun n => (W n).val) ∈ M) :
    sequenceGraph (fun n => internalCylinderUnion M (W n).val) ∈ M := by
  let G : M := ⟨_, hG⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let Y : M := ⟨_, hY⟩
  let values (n : ℕ) : M := ⟨_, internalCylinderUnion_mem hM hsep hY _ (W n).property⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep cylinderUnionSequencePredicate ![G, R, Y] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![G, R, Y]) (natOrdinal n)) y.val =
      ![G.val, R.val, Y.val, natOrdinal n, y.val] := by funext i; fin_cases i <;> rfl
  rw [he, eval_cylinderUnionSequencePredicate]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The internal clopen set determined by one finite binary-tree level. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $Y_M$ be the internal Cantor space from §{sec:internal-cantor-borel-sets}, and put
    $$\begin{aligned}
    \InternalTreeLevel{M}{T}{n}&:=\{g\in Y_M:\exists \sigma\in L_n\;(\sigma\IncludedIn g)\},\\
    \InternalTreeBody{M}{T}&:=\{g\in Y_M:\forall n\in\omega\;(g\in\InternalTreeLevel{M}{T}{n})\}.
    \end{aligned}$$
    The relation $\sigma\IncludedIn g$ says that the finite word is an initial segment of the point represented by $g$.
-/
def internalLevelSet (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ) : ZFSet.{u} :=
  internalCylinderUnion M (finiteWordLevel (binaryLift T) n)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Each element of $L_n$ is the graph of a unique binary word of length $n$. Its graph is contained in $g_{i(x)}$
    exactly when it is the length-$n$ prefix of $x$. This proves the first membership equivalence.
    Taking all lengths gives the second. The sets $C_n(T)$ are finite unions of clopen cylinders.
    Downward closure of $T$ implies $C_{n+1}(T)\IncludedIn C_n(T)$, and the first equivalence transfers this
    inclusion to their internal interpretations.
-/
lemma cantorPointGraph_mem_internalLevelSet (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ)
    (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalLevelSet M T n ↔ cantorPointGraph x ∈ M ∧ x ∈ levelSet T n := by
  rw [internalLevelSet, internalCylinderUnion, ZFSet.mem_sep, cantorPointGraph_mem_internalCantor]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨w, hw, hsub⟩
    obtain ⟨s, hs, he⟩ := mem_wordTreeSet.mp (ZFSet.mem_sep.mp hw).1
    obtain ⟨t, ht, rfl⟩ := hs
    rw [← he, wordGraph_mem_finiteWordLevel] at hw
    have hlen : t.length = n := by simpa only [List.length_map] using hw.2
    rw [← he] at hsub
    have hx := (wordGraph_subset_pointGraph (t.map Bool.toNat) (cantorInclusion x)).mp hsub
    have hx' : x ∈ cyl t := by
      change x ∈ cantorInclusion ⁻¹' cyl (t.map Bool.toNat) at hx
      rwa [BorelExpression.cantorInclusion_preimage_cyl] at hx
    have hp := seqPrefix_eq_of_mem_cyl hx'
    rw [hlen] at hp
    exact (mem_levelSet T n x).mpr (hp ▸ ht)
  · intro hx
    let t := seqPrefix x n
    have ht : t ∈ T := (mem_levelSet T n x).mp hx
    refine ⟨wordGraph (t.map Bool.toNat), ?_, ?_⟩
    · apply (wordGraph_mem_finiteWordLevel _ _ _).mpr
      exact ⟨⟨t, ht, rfl⟩, by simp [t, seqPrefix]⟩
    · apply (wordGraph_subset_pointGraph _ _).mpr
      change x ∈ cantorInclusion ⁻¹' cyl (t.map Bool.toNat)
      rw [BorelExpression.cantorInclusion_preimage_cyl]
      exact mem_cyl_seqPrefix x n

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal decreasing clopen approximation
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For any internal word family $W$, the predicate
    $$\exists \sigma\in W\;(\sigma\IncludedIn g)$$
    is bounded. Separation on $Y_M$ forms its cylinder union. Given the entire graph $G_L$, a bounded formula
    reads its value at $n$ and characterizes that union by its membership condition on $Y_M$.
    The same graph-collection theorem gives $G_C$.
    Its range belongs to $M$, so another bounded Separation forms
    $$\{g\in Y_M:\forall D\in\operatorname{ran}(G_C)\;(g\in D)\}=\InternalTreeBody{M}{T}.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The clopen sets in §{sec:internal-borel-measure-cut} form an entire internal sequence.
-/
theorem internalLevelSet_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) :
    sequenceGraph (internalLevelSet M T) ∈ M := by
  exact internalCylinderUnion_sequence_mem hM hinf hpair hunion hsep hrep
    (internalCantor_mem hM hinf hpair hunion hpower hsep)
    (fun n => ⟨_, finiteWordLevel_mem hM hinf hsep _ hT n⟩)
    (finiteWordLevel_sequence_mem hM hinf hpair hsep hrep _ hT)

lemma internalLevelSet_antitone (M : ZFSet.{u}) {T : Set (List Bool)} (hT : IsSubtree T)
    {m n : ℕ} (hmn : m ≤ n) : internalLevelSet M T n ⊆ internalLevelSet M T m := by
  intro g hg
  have hgY : g ∈ internalCantor M := by
    unfold internalLevelSet internalCylinderUnion at hg
    exact (ZFSet.mem_sep.mp hg).1
  obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp hgY
  rw [cantorPointGraph_mem_internalLevelSet] at hg ⊢
  exact ⟨hg.1, levelSet_antitone hT hmn hg.2⟩

lemma cantorPointGraph_mem_all_internalLevelSet (M : ZFSet.{u}) (T : Set (List Bool))
    (x : ℕ → Bool) :
    (∀ n, cantorPointGraph x ∈ internalLevelSet M T n) ↔
      cantorPointGraph x ∈ M ∧ x ∈ treeBody T := by
  simp only [cantorPointGraph_mem_internalLevelSet, mem_levelSet, mem_treeBody]
  exact ⟨fun h => ⟨(h 0).1, fun n => (h n).2⟩, fun h n => ⟨h.1, h.2 n⟩⟩

/-- The intersection uses the whole internal family, with the internal Cantor space as ambient set. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $Y_M$ be the internal Cantor space from §{sec:internal-cantor-borel-sets}, and put
    $$\begin{aligned}
    \InternalTreeLevel{M}{T}{n}&:=\{g\in Y_M:\exists \sigma\in L_n\;(\sigma\IncludedIn g)\},\\
    \InternalTreeBody{M}{T}&:=\{g\in Y_M:\forall n\in\omega\;(g\in\InternalTreeLevel{M}{T}{n})\}.
    \end{aligned}$$
    The relation $\sigma\IncludedIn g$ says that the finite word is an initial segment of the point represented by $g$.
-/
def internalLevelIntersection (M : ZFSet.{u}) (T : Set (List Bool)) : ZFSet.{u} :=
  (internalCantor M).sep (fun g => ∀ n, g ∈ internalLevelSet M T n)

lemma cantorPointGraph_mem_internalLevelIntersection (M : ZFSet.{u}) (T : Set (List Bool))
    (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalLevelIntersection M T ↔
      cantorPointGraph x ∈ M ∧ x ∈ treeBody T := by
  simp only [internalLevelIntersection, ZFSet.mem_sep, cantorPointGraph_mem_internalCantor,
    cantorPointGraph_mem_all_internalLevelSet, and_self_left]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal decreasing clopen approximation
-/
theorem internalLevelIntersection_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) :
    internalLevelIntersection M T ∈ M := by
  have hG := internalLevelSet_sequence_mem hM hinf hpair hunion hpower hsep hrep T hT
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let p : BoundedSetPredicate 2 := .all 0 (.member 1 2)
  apply separation_mem_of_absolute hM p.compile (hsep _) ![R]
    (internalCantor_mem hM hinf hpair hunion hpower hsep)
  intro g _
  rw [p.realize_compile hM]
  change (∀ A ∈ graphRange (sequenceGraph (internalLevelSet M T)), g.val ∈ A) ↔ _
  constructor
  · intro h n
    exact h _ (mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph _ n _).mpr rfl⟩)
  · intro h A hA
    obtain ⟨a, ha⟩ := mem_graphRange.mp hA
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp ha
    rw [← (ZFSet.pair_inj.mp hn).2]
    exact h n

end PolishSpaceBook.CantorTreeMeasure
