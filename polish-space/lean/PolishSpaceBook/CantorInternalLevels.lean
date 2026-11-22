module

public import PolishSpaceBook.SetTheoryFiniteCardinality
public import PolishSpaceBook.SetTheoryWordOperations
public import PolishSpaceBook.SetTheoryTreeRanks
public import PolishSpaceBook.BorelRankMeasureBounds

@[expose] public section

/-! # Exact finite levels of an internal binary tree -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression
open scoped Classical
universe u

/-- Recognize a level by the domain of each finite function graph. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For each $n\in\omega$, write
    $$L_n:=\{\sigma\in W_T:\sigma:n\to\omega\},\qquad k_n:=\Card{T_n}.$$
    Thus $L_n$ consists of the graphs of the words in the finite level $T_n$; it includes dead ends.
-/
def finiteWordLevel (T : Set (List ℕ)) (n : ℕ) : ZFSet.{u} :=
  (wordTreeSet T).sep (fun s => IsFunc (natOrdinal n) Ordinal.omega0.toZFSet s)

lemma wordGraph_mem_finiteWordLevel (T : Set (List ℕ)) (n : ℕ) (s : List ℕ) :
    wordGraph s ∈ finiteWordLevel.{u} T n ↔ s ∈ T ∧ s.length = n := by
  simp only [finiteWordLevel, ZFSet.mem_sep, wordGraph_mem_wordTreeSet, wordLength_iff, eq_comm]

/-- Separation selects the whole actual level, including dead ends. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal finite tree levels
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    Separate from $W_T$ the graphs $\sigma$ satisfying $\sigma:n\to\omega$. The finite-word length lemma identifies
    this predicate with having length $n$. Thus the separated set is precisely $W_{T,n}$.
-/
theorem finiteWordLevel_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List ℕ)) (hT : wordTreeSet T ∈ M) (n : ℕ) : finiteWordLevel T n ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let N : M := ⟨natOrdinal n, hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property⟩
  exact (BoundedSetPredicate.function (1 : Fin 3) 0 2).separation_mem hM (hsep _) ![Ω, N] hT

/-- Each finite binary assignment is the same node as its graph of zero-one natural values. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    Binary functions on $n$ correspond bijectively to binary words of length $n$, and coding a word by its graph
    is injective. Restricting this correspondence to $T$ shows that $|W_{T,n}|=|T_n|$.
-/
def binaryLevelEquiv (T : Set (List Bool)) (n : ℕ) :
    (level T n) ≃ finiteWordLevel.{u} (binaryLift T) n :=
  Equiv.ofBijective (fun s => ⟨wordGraph ((List.ofFn s.val).map Bool.toNat),
    (wordGraph_mem_finiteWordLevel _ _ _).mpr
      ⟨⟨List.ofFn s.val, (Finset.mem_filter.mp s.property).2, rfl⟩,
        by simp only [List.length_map, List.length_ofFn]⟩⟩) (by
    constructor
    · intro s t h
      have hm := wordGraph_injective (congrArg Subtype.val h)
      have hi : Function.Injective (List.map Bool.toNat) := List.map_injective_iff.mpr
        (fun a b h => by cases a <;> cases b <;> simp_all)
      exact Subtype.ext (List.ofFn_inj.mp (hi hm))
    · intro x
      obtain ⟨hxt, hlen⟩ := ZFSet.mem_sep.mp x.property
      obtain ⟨s, hs, he⟩ := mem_wordTreeSet.mp hxt
      obtain ⟨t, ht, rfl⟩ := hs
      rw [← he, wordLength_iff, List.length_map] at hlen
      subst n
      refine ⟨⟨fun i : Fin t.length => t.get i, ?_⟩, ?_⟩
      · simpa [level] using ht
      · apply Subtype.ext
        simpa using he)

/-- The internal finite-cardinality formula returns the exact external cylinder count. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal finite tree levels
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    Apply the finite-cardinality lemma. This counts the entire level, including nodes with no infinite extension;
    neither downward closure nor the existence of a branch is needed here.
-/
theorem binaryLevel_cardinality_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (T : Set (List Bool)) (n k : ℕ) (K A : M)
    (hK : K.val = natOrdinal k) (hA : A.val = finiteWordLevel (binaryLift T) n) :
    finiteCardinalityFormula.Realize Empty.elim ![K, A] ↔ k = (level T n).card := by
  let e : Fin (level T n).card ≃ finiteWordLevel.{u} (binaryLift T) n :=
    (Finset.equivFin (level T n)).symm.trans (binaryLevelEquiv T n)
  apply finiteCardinality_absolute hM hinf hpair hunion K A k _ hK
  simpa only [hA] using e

end PolishSpaceBook.CantorTreeMeasure
