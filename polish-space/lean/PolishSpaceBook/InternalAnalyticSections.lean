module

public import PolishSpaceBook.TreeBranchAbsoluteness
public import PolishSpaceBook.SetTheoryWordOperations
public import PolishSpaceBook.ClosedPairTreeGeometry

@[expose] public section

/-! # Internal sections of pair-tree presentations

A synchronized pair tree is coded by pairs of finite function graphs. Separating
the second coordinates whose first coordinate is an initial segment of the
parameter constructs its section inside the transitive model.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BorelExpression
universe u

/-- The set code records the actual pairs of finite-word graphs. -/
def pairWordTreeSet (T : Set (List ℕ × List ℕ)) : ZFSet.{u} :=
  ZFSet.range (fun z : T => pair (wordGraph z.val.1) (wordGraph z.val.2))

lemma pair_mem_pairWordTreeSet {T : Set (List ℕ × List ℕ)} (s t : List ℕ) :
    pair (wordGraph.{u} s) (wordGraph t) ∈ pairWordTreeSet T ↔ (s, t) ∈ T := by
  rw [pairWordTreeSet, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨a,b⟩, hab⟩, he⟩
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp he
    exact (wordGraph_injective ha) ▸ (wordGraph_injective hb) ▸ hab
  · intro h
    exact ⟨⟨(s,t),h⟩, rfl⟩

/-- A section retains exactly the finite approximations to the fixed first coordinate. -/
def analyticSection (T : Set (List ℕ × List ℕ)) (x : ℕ → ℕ) : Set (List ℕ) :=
  {s | (seqPrefix x s.length, s) ∈ T}

def analyticSectionPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.conj (.subset 4 2) (.pairMember 1 4 3))

/-- In parameters finiteSequences, pair-tree code, point graph, candidate word,
the reflected test is precisely membership in the section. -/
lemma eval_analyticSectionPredicate (T : Set (List ℕ × List ℕ))
    (hsync : ∀ z ∈ T, z.1.length = z.2.length) (x : ℕ → ℕ) (s : List ℕ) :
    analyticSectionPredicate.eval
      ![finiteSequences, pairWordTreeSet.{u} T, pointGraph x, wordGraph s] ↔ s ∈ analyticSection T x := by
  simp only [analyticSectionPredicate, BoundedSetPredicate.eval, Fin.snoc, Matrix.cons_val_zero]
  constructor
  · rintro ⟨a, ha, hsub, hpair⟩
    obtain ⟨t, rfl⟩ := (mem_finiteSequences.mp ha)
    have ht : (t,s) ∈ T := (pair_mem_pairWordTreeSet t s).mp hpair
    have hx := (wordGraph_subset_pointGraph t x).mp hsub
    have he := seqPrefix_eq_of_mem_cyl hx
    have hl := hsync (t,s) ht
    simpa only [analyticSection, Set.mem_ofPred_eq, ← hl, he] using ht
  · intro hs
    refine ⟨wordGraph (seqPrefix x s.length), ?_, ?_, ?_⟩
    · exact mem_finiteSequences.mpr ⟨seqPrefix x s.length, rfl⟩
    · exact (wordGraph_subset_pointGraph _ _).mpr (mem_cyl_seqPrefix x s.length)
    · exact (pair_mem_pairWordTreeSet _ _).mpr hs

/-- Separation constructs the whole set of section nodes, not just its individual words. -/
theorem analyticSection_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List ℕ × List ℕ)) (hsync : ∀ z ∈ T, z.1.length = z.2.length)
    (hT : pairWordTreeSet T ∈ M) (x : ℕ → ℕ) (hx : pointGraph x ∈ M) :
    wordTreeSet (analyticSection T x) ∈ M := by
  let S : M := ⟨finiteSequences, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let Q : M := ⟨pairWordTreeSet T, hT⟩
  let g : M := ⟨pointGraph x, hx⟩
  let P : ZFSet.{u} → Prop := fun z => ∃ a ∈ finiteSequences, a ⊆ pointGraph x ∧ pair a z ∈ pairWordTreeSet T
  have htest (s : List ℕ) : P (wordGraph s) ↔ s ∈ analyticSection T x := by
    exact eval_analyticSectionPredicate T hsync x s
  have hmem : finiteSequences.sep P ∈ M := by
    apply separation_mem_of_absolute hM analyticSectionPredicate.compile (hsep _) ![S,Q,g] S.property P
    intro z _
    rw [BoundedSetPredicate.realize_compile hM]
    rfl
  have he : finiteSequences.sep P = wordTreeSet (analyticSection T x) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_wordTreeSet]
    constructor
    · rintro ⟨hz, hp⟩
      obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hz
      exact ⟨s, (htest s).mp hp, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨mem_finiteSequences.mpr ⟨s,rfl⟩, (htest s).mpr hs⟩
  exact he ▸ hmem

/-- Prefix closure of the pair tree gives prefix closure of every section. -/
theorem analyticSection_subtree (T : Set (List ℕ × List ℕ))
    (hd : ∀ z ∈ T, ∀ n, (z.1.take n,z.2.take n) ∈ T) (x : ℕ → ℕ) :
    IsSubtree (analyticSection T x) := by
  intro s t ht hst
  have h := hd (seqPrefix x t.length,t) ht s.length
  have he := List.prefix_iff_eq_take.mp hst
  simpa only [analyticSection, Set.mem_ofPred_eq, seqPrefix_take_of_le _ hst.length_le, ← he] using h

/-- The branch through the section is exactly a witness in the closed pair-tree body. -/
theorem treeBody_analyticSection (T : Set (List ℕ × List ℕ)) (x y : ℕ → ℕ) :
    y ∈ treeBody (analyticSection T x) ↔ (x,y) ∈ pairTreeBody T := by
  simp only [treeBody, analyticSection, pairTreeBody, Set.mem_ofPred_eq, seqPrefix_length]

end PolishSpaceBook.SetTheoryModels
