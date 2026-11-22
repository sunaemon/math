module

public import PolishSpaceBook.NonnegativeRealCutInfimum
public import PolishSpaceBook.SetTheoryInternalSequenceSets
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-! # Unions of strict real cuts and bounded suprema -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels Filter Topology
universe u

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Unions of bounded real cuts
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For $b>0$, the inequality $a/b<\sup_n r_n$ holds exactly when $a/b<r_n$ for some $n$.
    This proves equality of the strict cuts. An increasing bounded real sequence converges to its supremum;
    uniqueness of limits and the encoding-decoding identities prove the equivalence.
-/
theorem sequenceUnion_realCuts (r : ℕ → ℝ) (hb : BddAbove (Set.range r)) :
    sequenceUnion (fun n => nonnegativeRealCutCode.{u} (r n)) = nonnegativeRealCutCode (⨆ n, r n) := by
  ext z
  rw [mem_sequenceUnion, mem_nonnegativeRealCutCode]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨a, b, rfl, hd, hl⟩ := (mem_nonnegativeRealCutCode _ _).mp hn
    exact ⟨a, b, rfl, hd, hl.trans_le (le_ciSup hb n)⟩
  · rintro ⟨a, b, rfl, hd, hl⟩
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hb).mp hl
    exact ⟨n, (pair_mem_nonnegativeRealCutCode _ a b).mpr ⟨hd, hn⟩⟩

lemma decode_sequenceUnion_realCuts (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hb : BddAbove (Set.range r)) :
    decodeNonnegativeRealCut (sequenceUnion (fun n => nonnegativeRealCutCode.{u} (r n))) = ⨆ n, r n := by
  rw [sequenceUnion_realCuts r hb, decode_nonnegativeRealCutCode ((hr 0).trans (le_ciSup hb 0))]

/-- A whole union equation for recognized codes yields convergence of their increasing decoded values. -/
theorem tendsto_decode_of_code_union (C : ℕ → ZFSet.{u}) (E : ZFSet.{u})
    (hC : ∀ n, ValidNonnegativeRealCutCode (C n)) (hE : ValidNonnegativeRealCutCode E)
    (hmono : Monotone (fun n => decodeNonnegativeRealCut (C n))) (he : E = sequenceUnion C) :
    Tendsto (fun n => decodeNonnegativeRealCut (C n)) atTop (𝓝 (decodeNonnegativeRealCut E)) := by
  have hb : BddAbove (Set.range (fun n => decodeNonnegativeRealCut (C n))) := by
    refine ⟨decodeNonnegativeRealCut E, ?_⟩
    rintro r ⟨n, rfl⟩
    apply (nonnegativeRealCutCode_subset_iff (decodeNonnegativeRealCut_nonneg hE)).mp
    rw [← (hC n).encode_decode, ← hE.encode_decode, he]
    intro z hz
    exact (mem_sequenceUnion C z).mpr ⟨n, hz⟩
  have hc : C = fun n => nonnegativeRealCutCode (decodeNonnegativeRealCut (C n)) :=
    funext (fun n => (hC n).encode_decode)
  have hv : decodeNonnegativeRealCut E = ⨆ n, decodeNonnegativeRealCut (C n) := by
    calc
      decodeNonnegativeRealCut E = decodeNonnegativeRealCut
          (sequenceUnion (fun n => nonnegativeRealCutCode (decodeNonnegativeRealCut (C n)))) :=
        congrArg decodeNonnegativeRealCut (he.trans (congrArg sequenceUnion hc))
      _ = _ := decode_sequenceUnion_realCuts _ (fun n => decodeNonnegativeRealCut_nonneg (hC n)) hb
  rw [hv]
  exact tendsto_atTop_ciSup hmono hb

lemma code_union_of_tendsto (C : ℕ → ZFSet.{u}) (E : ZFSet.{u})
    (hC : ∀ n, ValidNonnegativeRealCutCode (C n)) (hE : ValidNonnegativeRealCutCode E)
    (hmono : Monotone (fun n => decodeNonnegativeRealCut (C n)))
    (hb : BddAbove (Set.range (fun n => decodeNonnegativeRealCut (C n))))
    (ht : Tendsto (fun n => decodeNonnegativeRealCut (C n)) atTop (𝓝 (decodeNonnegativeRealCut E))) :
    E = sequenceUnion C := by
  have hv := tendsto_nhds_unique ht (tendsto_atTop_ciSup hmono hb)
  have hc : C = fun n => nonnegativeRealCutCode (decodeNonnegativeRealCut (C n)) :=
    funext (fun n => (hC n).encode_decode)
  calc
    E = nonnegativeRealCutCode (decodeNonnegativeRealCut E) := hE.encode_decode
    _ = nonnegativeRealCutCode (⨆ n, decodeNonnegativeRealCut (C n)) := congrArg nonnegativeRealCutCode hv
    _ = sequenceUnion C := (sequenceUnion_realCuts _ hb).symm.trans (congrArg sequenceUnion hc).symm

end PolishSpaceBook.CantorTreeMeasure
