module

public import PolishSpaceBook.BorelNodeCodes
public import PolishSpaceBook.BorelExpressionBoolean
public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Internal label graphs for Boolean operations and countable unions -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters: omega, zero, empty word, finite words, child table, its range, root label, word, value. -/
def graftLabelPredicate : BoundedSetPredicate 9 :=
  .disj (.conj (.equal 7 2) (.equal 8 6))
    (.ex 0 (.ex 3 (.ex 5 (.conj (wordConsPredicate.rename ![0, 1, 9, 10, 7])
      (.conj (.pairMember 4 9 11) (.pairMember 11 10 8))))))

lemma eval_graftLabelPredicate (a : ℕ) (c : ℕ → BorelExpression) (s : List ℕ) (y : ZFSet.{u}) :
    graftLabelPredicate.eval ![Ordinal.omega0.toZFSet, natOrdinal 0, wordGraph [], finiteSequences,
      sequenceGraph (fun n => (c n).labelGraph), graphRange (sequenceGraph (fun n => (c n).labelGraph)),
      natOrdinal a, wordGraph s, y] ↔ y = natOrdinal (graft a c s) := by
  simp only [graftLabelPredicate, eval, eval_rename, Fin.snoc]
  change ((wordGraph s = wordGraph [] ∧ y = natOrdinal a) ∨
    ∃ n ∈ Ordinal.omega0.toZFSet, ∃ t ∈ finiteSequences,
      ∃ C ∈ graphRange (sequenceGraph (fun n => (c n).labelGraph)),
        SetWordCons Ordinal.omega0.toZFSet (natOrdinal 0) n t (wordGraph s) ∧
        pair n C ∈ sequenceGraph (fun n => (c n).labelGraph) ∧ pair t y ∈ C) ↔ _
  constructor
  · rintro (⟨hs, hy⟩ | ⟨N, hN, t, ht, C, _, hs, hC, hy⟩)
    · have he := wordGraph_injective.{u} hs
      simpa [he] using hy
    · obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hN
      obtain ⟨v, rfl⟩ := mem_finiteSequences.mp ht
      have he := (setWordCons_wordGraph_iff n v s).mp hs
      have hC' := (pair_mem_sequenceGraph _ n C).mp hC
      subst C
      rw [he, graft_cons]
      exact (pair_mem_labelGraph _ _ _).mp hy
  · intro hy
    cases s with
    | nil => exact Or.inl ⟨rfl, hy⟩
    | cons n t =>
      refine Or.inr ⟨natOrdinal n, mem_omegaOrdinal.mpr ⟨n, rfl⟩, wordGraph t,
        mem_finiteSequences.mpr ⟨t, rfl⟩, (c n).labelGraph, ?_, ?_, ?_, ?_⟩
      · exact mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph _ n _).mpr rfl⟩
      · exact (setWordCons_wordGraph_iff n t (n :: t)).mpr rfl
      · exact (pair_mem_sequenceGraph _ n _).mpr rfl
      · exact (pair_mem_labelGraph _ _ _).mpr hy

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal Boolean code constructors
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Use the finite-word graphs and the cons predicate of §{sec:internal-list-coding}.
    For a fixed root label $a$ and child table $H$, the grafted labels are
    $$g([])=a,\qquad g(n::s)=c_n(s).$$
    The root case is a finite equality test. In the other case, bound $n$ by $\omega$, the tail by the internal
    finite-word set, and the child graph by the range of $H$.
    The cons predicate recognizes the input word, and two graph lookups recover the child graph and its label.
    This is a bounded predicate. The shared reflection theorem and graph collection therefore put the whole
    label graph of $g$ in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    For a complement, take root label $2$, put $c$ at child $0$, and use the absent expression at every other child.
    Its child table is defined by the two cases $n=0$ and $n\ne0$, so the same graph-collection principle constructs it.
    For a union, take root label $1$ and use $H$ directly.
    Finite unions use a two-valued child table; complements and finite unions then give intersections,
    differences, and symmetric differences.
    Their validity and interpretation equations follow from the complement and union equations
    in §{sec:borel-codes-why}.
-/
lemma graft_labelGraph_mem (a : ℕ) (c : ℕ → BorelExpression)
    (hc : sequenceGraph (fun n => (c n).labelGraph) ∈ M) : (graft a c).labelGraph ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let W : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let H : M := ⟨_, hc⟩
  let T : M := ⟨_, graphRange_mem hM hunion (hsep _) H.property⟩
  let ps : Fin 7 → M := ![Ω, ⟨natOrdinal 0, hn 0⟩,
    ⟨wordGraph [], hM.mem_trans (mem_finiteSequences.mpr ⟨[], rfl⟩) W.property⟩, W, H, T, ⟨natOrdinal a, hn a⟩]
  apply bounded_labelGraph_mem hM hinf hpair hunion hpower hsep hrep graftLabelPredicate ps (graft a c)
  intro s y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (wordGraph s)) y.val =
      ![Ordinal.omega0.toZFSet, natOrdinal 0, wordGraph [], finiteSequences,
        sequenceGraph (fun n => (c n).labelGraph), graphRange (sequenceGraph (fun n => (c n).labelGraph)),
        natOrdinal a, wordGraph s, y.val] := by funext i; fin_cases i <;> rfl
  rw [he, eval_graftLabelPredicate]

include hM hinf hpair hunion hpower hsep hrep in
lemma absent_labelGraph_mem : (absent.labelGraph : ZFSet.{u}) ∈ M := by
  let z : M := ⟨natOrdinal 0, hM.mem_trans (mem_omegaOrdinal.mpr ⟨0, rfl⟩)
    (omegaOrdinal_mem hM hinf (hsep _))⟩
  apply bounded_labelGraph_mem hM hinf hpair hunion hpower hsep hrep (.equal 2 0) ![z] absent
  intro s y
  rfl

include hM hinf hpair hsep hrep in
lemma binaryChoice_sequenceGraph_mem (a b : M) :
    sequenceGraph (fun n : ℕ => if n = 0 then a.val else b.val) ∈ M := by
  let z : M := ⟨natOrdinal 0, hM.mem_trans (mem_omegaOrdinal.mpr ⟨0, rfl⟩)
    (omegaOrdinal_mem hM hinf (hsep _))⟩
  let p : BoundedSetPredicate 5 :=
    .disj (.conj (.equal 3 0) (.equal 4 1)) (.conj (.neg (.equal 3 0)) (.equal 4 2))
  have hh := bounded_sequenceGraph_mem hM hinf hpair hsep hrep p ![z, a, b]
    (fun n : ℕ => if n = 0 then a else b) (by
      intro n y
      change ((natOrdinal n = natOrdinal 0 ∧ y.val = a.val) ∨
        (¬natOrdinal n = natOrdinal 0 ∧ y.val = b.val)) ↔ y = if n = 0 then a else b
      simp only [natOrdinal_injective.{u}.eq_iff, Subtype.val_inj]
      by_cases hn : n = 0 <;> simp [hn])
  simpa only [apply_ite Subtype.val] using hh

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal Boolean code constructors
-/
lemma complement_labelGraph_mem (c : BorelExpression) (hc : c.labelGraph ∈ M) :
    (complement c).labelGraph ∈ M := by
  apply graft_labelGraph_mem hM hinf hpair hunion hpower hsep hrep
  have hh := binaryChoice_sequenceGraph_mem hM hinf hpair hsep hrep ⟨c.labelGraph, hc⟩
    ⟨absent.labelGraph, absent_labelGraph_mem hM hinf hpair hunion hpower hsep hrep⟩
  simpa only [apply_ite labelGraph] using hh

namespace Code
include hM hinf hpair hunion hpower hsep hrep

lemma compl_labelGraph_mem (c : Code) (hc : c.val.labelGraph ∈ M) : c.compl.val.labelGraph ∈ M :=
  complement_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c.val hc

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal Boolean code constructors
-/
lemma iUnion_labelGraph_mem (c : ℕ → Code) (hc : sequenceGraph (fun n => (c n).val.labelGraph) ∈ M) :
    (iUnion c).val.labelGraph ∈ M :=
  graft_labelGraph_mem hM hinf hpair hunion hpower hsep hrep 1 _ hc

lemma sup_labelGraph_mem (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M) :
    (sup c d).val.labelGraph ∈ M := by
  apply iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep
  have hh := binaryChoice_sequenceGraph_mem hM hinf hpair hsep hrep ⟨c.val.labelGraph, hc⟩ ⟨d.val.labelGraph, hd⟩
  simpa only [apply_ite Subtype.val, apply_ite labelGraph] using hh

lemma inf_labelGraph_mem (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M) :
    (inf c d).val.labelGraph ∈ M :=
  compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
    (sup_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _
      (compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc)
      (compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep d hd))

lemma diff_labelGraph_mem (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M) :
    (diff c d).val.labelGraph ∈ M :=
  inf_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c d.compl hc
    (compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep d hd)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal Boolean code constructors
-/
lemma symmDiff_labelGraph_mem (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M) :
    (symmDiff c d).val.labelGraph ∈ M :=
  sup_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _
    (diff_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c d hc hd)
    (diff_labelGraph_mem hM hinf hpair hunion hpower hsep hrep d c hd hc)

end Code
end PolishSpaceBook.BorelExpression
